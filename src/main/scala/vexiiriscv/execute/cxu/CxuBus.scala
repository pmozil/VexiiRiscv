package vexiiriscv.execute.cxu

import spinal.core._
import spinal.lib._
import spinal.lib.bus.bmb.WeakConnector
import spinal.lib.bus.misc.{AddressMapping, DefaultMapping}
import spinal.lib.misc.plugin.FiberPlugin
import spinal.lib.misc.pipeline._
import vexiiriscv.decode.{Decode, DecoderService}
import vexiiriscv.execute.{CsrService, LaneLayer, WriteBackPlugin}
import vexiiriscv.riscv.{IMM, IntRegFile, RD, RS1, RS2, RegfileSpec, Resource, SingleDecoding}

import scala.collection.mutable.ArrayBuffer


case class CxuBusParameter(
  CXU_VERSION: Int = 0,
  CXU_INTERFACE_ID_W: Int = 0,
  CXU_FUNCTION_ID_W: Int,
  CXU_REORDER_ID_W: Int = 0,
  CXU_REQ_RESP_ID_W: Int = 0,
  CXU_CXU_ID_W: Int = 0,
  CXU_STATE_INDEX_NUM: Int = 0,
  CXU_INPUTS: Int,
  CXU_INPUT_DATA_W: Int,
  CXU_OUTPUTS: Int,
  CXU_OUTPUT_DATA_W: Int,
  CXU_FLOW_REQ_READY_ALWAYS: Boolean,
  CXU_FLOW_RESP_READY_ALWAYS: Boolean,
  CXU_WITH_STATUS: Boolean = false,
  CXU_RAW_INSN_W: Int = 0,
  CXU_L0_COUNT: Int = 0,
  CXU_L1_COUNT: Int = 0,
  CXU_L2_COUNT: Int = 0,
  CXU_L3_COUNT: Int = 0,
  CXU_FEATURE_LEVEL: Int = 0,
  CXU_MAX_PENDING_REQUESTS: Int = 1
)

case class CxuCmd(p: CxuBusParameter) extends Bundle {
  val function_id = UInt(p.CXU_FUNCTION_ID_W bits)
  val reorder_id = UInt(p.CXU_REORDER_ID_W bits)
  val request_id = UInt(p.CXU_REQ_RESP_ID_W bits)
  val inputs = Vec(Bits(p.CXU_INPUT_DATA_W bits), p.CXU_INPUTS)
  val state_id = UInt(log2Up(p.CXU_STATE_INDEX_NUM) bits)
  val cxu_id = UInt(p.CXU_CXU_ID_W bits)
  val raw_insn = Bits(p.CXU_RAW_INSN_W bits)
  val ready = p.CXU_FEATURE_LEVEL >= 2 generate Bool()

  def weakAssignFrom(m: CxuCmd): Unit = {
    def s = this
    WeakConnector(m, s, m.function_id, s.function_id, defaultValue = null, allowUpSize = false, allowDownSize = true, allowDrop = true)
    WeakConnector(m, s, m.reorder_id, s.reorder_id, defaultValue = null, allowUpSize = false, allowDownSize = false, allowDrop = false)
    WeakConnector(m, s, m.request_id, s.request_id, defaultValue = null, allowUpSize = false, allowDownSize = false, allowDrop = false)
    s.inputs := m.inputs
    if(p.CXU_FEATURE_LEVEL >= 2) s.ready := m.ready
  }
}

case class CxuRsp(p: CxuBusParameter) extends Bundle {
  val response_id = UInt(p.CXU_REQ_RESP_ID_W bits)
  val outputs = Vec(Bits(p.CXU_OUTPUT_DATA_W bits), p.CXU_OUTPUTS)
  val status = p.CXU_WITH_STATUS generate Bits(32 bits)
  val ready = p.CXU_FEATURE_LEVEL >= 2 generate Bool()

  def weakAssignFrom(m: CxuRsp): Unit = {
    def s = this
    s.response_id := m.response_id
    s.outputs := m.outputs
    if(p.CXU_WITH_STATUS) s.status := m.status
    if(p.CXU_FEATURE_LEVEL >= 2) s.ready := m.ready
  }
}

case class CxuBus(p: CxuBusParameter) extends Bundle with IMasterSlave {
  val cmd = Stream(CxuCmd(p))
  val rsp = Stream(CxuRsp(p))

  def <<(m: CxuBus): Unit = {
    val s = this
    s.cmd.arbitrationFrom(m.cmd)
    m.rsp.arbitrationFrom(s.rsp)

    s.cmd.weakAssignFrom(m.cmd)
    m.rsp.weakAssignFrom(s.rsp)
  }

  override def asMaster(): Unit = {
    master(cmd)
    slave(rsp)
  }
}


case class CxuMux(p: CxuBusParameter) extends Bundle with IMasterSlave {
  val cmd = Stream(CxuCmd(p))
  val rsp = Stream(CxuRsp(p))

  override def asMaster(): Unit = {
    master(cmd)
    slave(rsp)
  }

  val totalCxuCount = p.CXU_L0_COUNT + p.CXU_L1_COUNT + p.CXU_L2_COUNT + p.CXU_L3_COUNT
  val selected = Reg(UInt(log2Up(totalCxuCount) bits)) init(0)

  val buses = for (i <- 0 until totalCxuCount) yield new Area {
    val level = if (i < p.CXU_L0_COUNT) 0
                else if (i < p.CXU_L0_COUNT + p.CXU_L1_COUNT) 1
                else if (i < p.CXU_L0_COUNT + p.CXU_L1_COUNT + p.CXU_L2_COUNT) 2
                else 3
    val customParam = p.copy(CXU_FEATURE_LEVEL = level)
    val bus = CxuBus(customParam)
  }

  val flatBuses = buses.map(_.bus)

  if (p.CXU_FEATURE_LEVEL >= 2) {
    cmd.ready := False
    cmd.payload.ready := False
    rsp.payload.ready := False
  }

  for ((bus, i) <- flatBuses.zipWithIndex) {
    val isSelected = selected === U(i, selected.getWidth bits)

    bus.cmd.valid := cmd.valid && isSelected
    bus.cmd.payload := cmd.payload
    when(isSelected) {
      cmd.ready := bus.cmd.ready
      if (p.CXU_FEATURE_LEVEL >= 2) cmd.payload.ready := bus.cmd.payload.ready
    }

    val matchedRsp = bus.rsp.valid && isSelected
    rsp.valid := matchedRsp
    when(matchedRsp) {
      rsp.payload := bus.rsp.payload
    }
    bus.rsp.ready := rsp.ready && isSelected
    when(isSelected) {
      if (p.CXU_FEATURE_LEVEL >= 2) rsp.payload.ready := bus.rsp.payload.ready
    }
  }
}
