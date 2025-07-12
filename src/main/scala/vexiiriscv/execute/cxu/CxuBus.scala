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
  CXU_CXU_ID_W: Int = 0,
  CXU_REORDER_ID_W: Int = 0,
  CXU_REQ_RESP_ID_W: Int = 0,
  CXU_STATE_INDEX_NUM: Int = 0,
  CXU_INPUTS: Int,
  CXU_INPUT_DATA_W: Int,
  CXU_OUTPUTS: Int,
  CXU_OUTPUT_DATA_W: Int,
  CXU_FLOW_REQ_READY_ALWAYS: Boolean,
  CXU_FLOW_RESP_READY_ALWAYS: Boolean,
  CXU_WITH_STATUS: Boolean = false,
  CXU_RAW_INSN_W: Int = 0,
  CXU_L0_COUNT: Int = 1,
  CXU_L1_COUNT: Int = 0,
  CXU_L2_COUNT: Int = 0,
  CXU_L3_COUNT: Int = 0
)

case class CxuCmd(p: CxuBusParameter) extends Bundle {
  val function_id = UInt(p.CXU_FUNCTION_ID_W bits)
  val reorder_id = UInt(p.CXU_REORDER_ID_W bits)
  val request_id = UInt(p.CXU_REQ_RESP_ID_W bits)
  val inputs = Vec(Bits(p.CXU_INPUT_DATA_W bits), p.CXU_INPUTS)
  val state_id = UInt(log2Up(p.CXU_STATE_INDEX_NUM) bits)
  val cxu_id = UInt(p.CXU_CXU_ID_W bits)
  val raw_insn = Bits(p.CXU_RAW_INSN_W bits)

  def weakAssignFrom(m: CxuCmd): Unit = {
    def s = this
    WeakConnector(m, s, m.function_id, s.function_id, defaultValue = null, allowUpSize = false, allowDownSize = true, allowDrop = true)
    WeakConnector(m, s, m.reorder_id, s.reorder_id, defaultValue = null, allowUpSize = false, allowDownSize = false, allowDrop = false)
    WeakConnector(m, s, m.request_id, s.request_id, defaultValue = null, allowUpSize = false, allowDownSize = false, allowDrop = false)
    s.inputs := m.inputs
  }
}

case class CxuRsp(p: CxuBusParameter) extends Bundle {
  val response_id = UInt(p.CXU_REQ_RESP_ID_W bits)
  val outputs = Vec(Bits(p.CXU_OUTPUT_DATA_W bits), p.CXU_OUTPUTS)
  val status = p.CXU_WITH_STATUS generate Bits(32 bits)

  def weakAssignFrom(m: CxuRsp): Unit = {
    def s = this
    s.response_id := m.response_id
    s.outputs := m.outputs
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
  val buses = Vec(CxuBus(p), totalCxuCount)
  val selected = Reg(UInt(log2Up(totalCxuCount) bits)) init(0)

  for ((bus, i) <- buses.zipWithIndex) {
    val isSelected = selected === U(i, selected.getWidth bits)

    bus.cmd.valid := cmd.valid && isSelected
    bus.cmd.payload := cmd.payload
    cmd.ready := bus.cmd.ready && isSelected

    val matchedRsp = bus.rsp.valid && isSelected
    rsp.valid := matchedRsp
    rsp.payload := bus.rsp.payload
    bus.rsp.ready := rsp.ready && isSelected
  }
}
