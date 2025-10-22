package vexiiriscv.execute.cxu

import spinal.core._
import spinal.lib._
import spinal.lib.bus.misc.DefaultMapping
import spinal.lib.misc.plugin.FiberPlugin
import spinal.lib.misc.pipeline._
import vexiiriscv.decode.{Decode, DecoderService}
import vexiiriscv.execute.{CsrService, LaneLayer, WriteBackPlugin}
import vexiiriscv.riscv.{IMM, IntRegFile, RD, RS1, RS2, RegfileSpec, Resource, SingleDecoding}

import scala.collection.mutable.ArrayBuffer

case class CxuPluginParameter(
                               CXU_VERSION : Int,
                               CXU_INTERFACE_ID_W : Int,
                               CXU_FUNCTION_ID_W : Int,
                               CXU_REORDER_ID_W : Int,
                               CXU_REQ_RESP_ID_W : Int,
                               CXU_INPUTS : Int,
                               CXU_INPUT_DATA_W : Int,
                               CXU_OUTPUTS : Int,
                               CXU_OUTPUT_DATA_W : Int,
                               CXU_FLOW_REQ_READY_ALWAYS : Boolean,
                               CXU_FLOW_RESP_READY_ALWAYS : Boolean,
                               CXU_WITH_STATUS: Boolean = false,
                               CXU_CXU_ID_W: Int = 8,
                               CXU_STATE_INDEX_NUM: Int = 1)

object CxuPlugin {
  object Input2Kind extends SpinalEnum {
    val RS, IMM_I = newElement()
  }
}

case class CxuPluginEncoding(instruction: MaskedLiteral,
                              functionId: List[Range],
                              input2Kind: CxuPlugin.Input2Kind.E) {
  val functionIdWidth = functionId.map(_.size).sum
}

class CxuPlugin(val layer: LaneLayer,
                val forkAt: Int,
                val joinAt: Int,
                val allowZeroLatency: Boolean,
                val busParameter: CxuBusParameter,
                val encodings: List[CxuPluginEncoding] = null,
                val stateAndIndexCsrOffset: Int = 0xBC0,
                val statusCsrOffset: Int = 0x801,
                val withEnable: Boolean = false,
                val enableInit: Boolean = false) extends FiberPlugin {
  def p = busParameter
  import CxuPlugin._

  assert(p.CXU_INPUTS <= 2)
  assert(p.CXU_OUTPUTS == 1)


  val logic = during setup new Area {
    val wbp = host.find[WriteBackPlugin](p => p.rf == IntRegFile && p.lane == layer.lane)
    val cp = host[CsrService]
    val ds = host[DecoderService]
    val earlyLock = retains(layer.lane.uopLock, wbp.elaborationLock, ds.decodingLock)
    val lateLock = retains(List(layer.lane.pipelineLock, cp.csrLock))
    awaitBuild()

    val cxuBus = master(CxuBus(p))

    val mcx_version = Reg(UInt(3 bits)) init(1)
    val mcx_cxe = Reg(Bool()) init(False)
    val mcx_state_id = Reg(UInt(log2Up(p.CXU_STATE_INDEX_NUM) bits)) init(0)
    val mcx_selector = out(Reg(UInt(p.CXU_CXU_ID_W bits)))

    when(mcx_version =/= 1) {
      mcx_selector := 0
    }

    val CXU_ENABLE = Payload(Bool())
    val CXU_IN_FLIGHT = Payload(Bool())
    val CXU_ENCODING = Payload(UInt(log2Up(encodings.size) bits))
    val CXU_INPUT_2_KIND = Payload(Input2Kind())

    val wb = wbp.createPort(at = joinAt)

    layer.lane.setDecodingDefault(CXU_ENABLE, False)
    if(withEnable) ds.addMicroOpDecodingDefault(CXU_ENABLE, False)

    val en = withEnable generate (Reg(Bool()) init(enableInit))

    val mappings = for ((encoding, id) <- encodings.zipWithIndex) yield new Area {
      val ressources = ArrayBuffer[Resource]()
      ressources += IntRegFile -> RD
      ressources += IntRegFile -> RS1
      encoding.input2Kind match {
        case Input2Kind.RS => ressources += IntRegFile -> RS2
        case _ =>
      }
      val uopType = SingleDecoding(
        key = encoding.instruction,
        resources = ressources
      )

      val uop = layer.add(uopType)
      uop.addRsSpec(RS1, executeAt = 0)
      encoding.input2Kind match {
        case Input2Kind.RS => uop.addRsSpec(RS2, executeAt = 0)
        case _ =>
      }
      uop.setCompletion(joinAt)
      uop.addDecoding(CXU_ENABLE -> True)
      uop.addDecoding(CXU_ENCODING -> U(id))
      uop.addDecoding(CXU_INPUT_2_KIND -> encoding.input2Kind(native))
      uop.dontFlushFrom(forkAt)

      wbp.addMicroOp(wb, uop)
      if(withEnable) ds.addMicroOpDecoding(uopType, CXU_ENABLE, True)
    }

    if(withEnable) ds.addDecodingLogic { ctx =>
      ctx.legal clearWhen(ctx.node(CXU_ENABLE) && !en)
    }

    earlyLock.release()

    val csr = new Area {
      cp.flushOnWrite(stateAndIndexCsrOffset)
      if(withEnable) cp.readWrite(stateAndIndexCsrOffset, 31 -> en)
      cp.readWrite(stateAndIndexCsrOffset, 29 -> mcx_version)
      cp.readWrite(stateAndIndexCsrOffset, 28 -> mcx_cxe)
      cp.readWrite(stateAndIndexCsrOffset, 16 -> mcx_state_id)
      cp.readWrite(stateAndIndexCsrOffset, 0 -> mcx_selector)

      val status = p.CXU_WITH_STATUS generate new Area {
        val IV = RegInit(False)
        val IC = RegInit(False)
        val IS = RegInit(False)
        val OF = RegInit(False)
        val IF = RegInit(False)
        val OP = RegInit(False)
        val CU = RegInit(False)
        val flags = List(CU, OP, IF, OF, IS, IC, IV).reverse
        cp.readWrite(statusCsrOffset,
          0 -> IV,
          1 -> IC,
          2 -> IS,
          3 -> OF,
          4 -> IF,
          5 -> OP,
          6 -> CU
        )
        cp.flushOnWrite(statusCsrOffset)
      }
    }

    val onFork = new layer.Execute(forkAt) {
      val schedule = isValid && CXU_ENABLE

      val hold = False
      val fired = RegInit(False) setWhen(cxuBus.cmd.fire) clearWhen(!layer.lane.isFreezed())
      CXU_IN_FLIGHT := schedule || hold || fired

      cxuBus.cmd.valid := (schedule || hold) && !fired
      cxuBus.cmd.cxu_id := mcx_selector
      cxuBus.cmd.state_id := mcx_state_id

      val freezeIt = cxuBus.cmd.valid && !cxuBus.cmd.ready
      layer.lane.freezeWhen(freezeIt)

      val functionIdFromInstructionWidth = encodings.map(_.functionIdWidth).max
      val functionsIds = encodings.map(e => U(Cat(e.functionId.map(r => Decode.UOP(r))), functionIdFromInstructionWidth bits))
      cxuBus.cmd.function_id := functionsIds.read(CXU_ENCODING)
      cxuBus.cmd.reorder_id := 0
      cxuBus.cmd.request_id := 0
      cxuBus.cmd.raw_insn := Decode.UOP.resized
      if(p.CXU_INPUTS >= 1) cxuBus.cmd.inputs(0) := up(layer.lane(IntRegFile, RS1))
      if(p.CXU_INPUTS >= 2) cxuBus.cmd.inputs(1) := CXU_INPUT_2_KIND.mux[Bits](
        Input2Kind.RS -> up(layer.lane(IntRegFile, RS2)),
        Input2Kind.IMM_I -> IMM(Decode.UOP).h_sext.asBits
      )

      val pendingRequests = p.CXU_FEATURE_LEVEL >= 2 generate new Area {
        val count = Reg(UInt(log2Up(p.CXU_MAX_PENDING_REQUESTS + 1) bits)) init(0)
        val full = count === p.CXU_MAX_PENDING_REQUESTS

        when(cxuBus.cmd.fire && !cxuBus.rsp.fire) { count := count + 1 }
        when(!cxuBus.cmd.fire && cxuBus.rsp.fire) { count := count - 1 }

        cxuBus.cmd.payload.ready := !full
      }
    }

    val onJoin = new layer.Execute(joinAt) {
      val busRspStream: Stream[CxuRsp] = cxuBus.rsp.toFlow.toStream
      val rsp = busRspStream.queueLowLatency(
        size = joinAt - forkAt + 1,
        latency = 0
      )

      val freezeIt = CXU_IN_FLIGHT && !rsp.valid
      layer.lane.freezeWhen(freezeIt)
      rsp.ready := CXU_IN_FLIGHT && !layer.lane.isFreezed()

      wb.valid := isValid && CXU_ENABLE
      wb.payload := rsp.outputs(0)

      if (p.CXU_WITH_STATUS) {
        when(isValid && isReady && !isCancel && CXU_ENABLE) {
          switch(rsp.status) {
            for (i <- 1 to 7) is(i) {
              csr.status.flags(i - 1) := True
            }
          }
        }
      }
   }

    for (eid <- forkAt + 1 to joinAt) {
      layer.lane.execute(eid).up(CXU_IN_FLIGHT).setAsReg().init(False)
    }

    lateLock.release()
  }
}
