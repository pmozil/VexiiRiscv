package vexiiriscv.soc

import net.fornwall.jelf.{ElfFile, ElfSection, ElfSectionHeader}
import spinal.core
import spinal.core._
import spinal.lib.misc._
import spinal.core.fiber._
import spinal.lib.{DataCc, StreamCCByToggle}
import spinal.lib.bus.tilelink.fabric._
import spinal.lib.cpu.riscv.RiscvHart
import spinal.lib.cpu.riscv.debug.DebugHartBus
import spinal.lib.misc.aia._
import spinal.lib.misc.InterruptCtrlFiber
import spinal.lib.misc.plugin.Hostable
import spinal.lib.misc.{ClintPort, Elf, InterruptCtrl, InterruptNode, TilelinkClintFiber}
import spinal.lib.sim.SparseMemory
import spinal.lib.system.tag.{MemoryConnection, PMA, PmaRegion}
import spinal.sim.{Signal, SimManagerContext}
import vexiiriscv.{ParamSimple, VexiiRiscv}
import vexiiriscv.execute.{CsrService}
import vexiiriscv.execute.cfu.{CfuBus, CfuBusParameter, CfuPlugin, CfuPluginEncoding}
import vexiiriscv.execute.cxu.{CxuBus, CxuBusParameter, CxuPlugin, CxuPluginEncoding, CxuMux}
import vexiiriscv.execute.lsu.{LsuCachelessPlugin, LsuCachelessTileLinkPlugin, LsuL1Plugin, LsuL1TileLinkPlugin, LsuPlugin, LsuTileLinkPlugin}
import vexiiriscv.fetch.{FetchCachelessPlugin, FetchCachelessTileLinkPlugin, FetchL1TileLinkPlugin, FetchL1Plugin}
import vexiiriscv.memory.AddressTranslationService
import vexiiriscv.misc.PrivilegedPlugin
import vexiiriscv.riscv.{PrivilegeMode, Riscv}

import java.io.{BufferedWriter, File, FileWriter}
import java.nio.file.Files
import scala.collection.mutable.ArrayBuffer

/**
 * Integration layer of VexiiRiscv into the fiber / tilelink framework
 * See the MicroSoc for a simple integration example.
 */
class TilelinkVexiiRiscvFiber(val plugins : ArrayBuffer[Hostable]) extends Area with RiscvHart{
  val iBus = Node.down()
  val dBus = Node.down()
  val lsuL1Bus = plugins.exists(_.isInstanceOf[LsuL1Plugin]) generate Node.down()
  val cfuBus = plugins.exists(_.isInstanceOf[CfuPlugin]) generate new Area {
    val cfuPlugin = plugins.find(_.isInstanceOf[CfuPlugin]).get.asInstanceOf[CfuPlugin]
    val cfuBusParam = cfuPlugin.busParameter
    val node = CfuBus(cfuBusParam)

    val cmd_valid = out(node.cmd.valid)
    val cmd_ready = in(node.cmd.ready)
    val cmd_payload_function_id = out(node.cmd.function_id)
    val cmd_payload_inputs_0 = out(node.cmd.inputs(0))
    val cmd_payload_inputs_1 = out(node.cmd.inputs(1))

    val rsp_valid = in(node.rsp.valid)
    val rsp_ready = out(node.rsp.ready)
    val rsp_payload_outputs_0 = in(node.rsp.outputs(0))
  }

  val cxuBus = plugins.exists(_.isInstanceOf[CxuPlugin]) generate new Area {
    val cxuPlugin = plugins.find(_.isInstanceOf[CxuPlugin]).get.asInstanceOf[CxuPlugin]
    val p = cxuPlugin.p

    val totalCxuCount = p.CXU_L0_COUNT + p.CXU_L1_COUNT + p.CXU_L2_COUNT + p.CXU_L3_COUNT

    val buses = (0 until totalCxuCount).map { i =>
      val level = 2
        // if (i < p.CXU_L0_COUNT) 0
        // else if (i < p.CXU_L0_COUNT + p.CXU_L1_COUNT) 1
        // else if (i < p.CXU_L0_COUNT + p.CXU_L1_COUNT + p.CXU_L2_COUNT) 2
        // else 3

      val customParam = p.copy(CXU_FEATURE_LEVEL = level)
      val busNode = CxuBus(customParam)

      new Area {
        val node = busNode

        val cmd_valid = out(node.cmd.valid)
        val cmd_ready = in(node.cmd.ready)
        val cmd_payload_cxu_id = out(node.cmd.cxu_id)
        val cmd_payload_state_id = out(node.cmd.state_id)
        val cmd_payload_function_id = out(node.cmd.function_id)
        val cmd_payload_reorder_id = out(node.cmd.reorder_id)
        val cmd_payload_request_id = out(node.cmd.request_id)
        val cmd_payload_raw_insn = out(node.cmd.raw_insn)
        val cmd_payload_inputs_0 = if(p.CXU_INPUTS >= 1) Some(out(node.cmd.inputs(0))) else None
        val cmd_payload_inputs_1 = if(p.CXU_INPUTS >= 2) Some(out(node.cmd.inputs(1))) else None
        val cmd_payload_ready = if(p.CXU_FEATURE_LEVEL >= 2) Some(out(node.cmd.payload.ready)) else None

        val rsp_valid = in(node.rsp.valid)
        val rsp_ready = out(node.rsp.ready)
        val rsp_payload_outputs_0 = if(p.CXU_OUTPUTS >= 1) Some(in(node.rsp.outputs(0))) else None
        val rsp_payload_status = if(p.CXU_WITH_STATUS) Some(in(node.rsp.status)) else None
        val rsp_payload_ready = if(p.CXU_FEATURE_LEVEL >= 2) Some(in(node.rsp.payload.ready)) else None
      }
    }

    val mcx_selector = UInt(p.CXU_CXU_ID_W bits)
  }

  def buses = List(iBus, dBus) ++ lsuL1Bus.nullOption

  val priv = plugins.collectFirst {
    case p: PrivilegedPlugin => new Area {
      val plugin = p
      val mti, msi, mei = InterruptNode.slave()
      val sei = p.p.withSupervisor generate InterruptNode.slave()
      val stoptime = Bool()
      val rdtime = p.p.withRdTime generate UInt(64 bits)
      val mmsi = p.p.withImsic generate Bits(p.p.imsicInterrupts - 1 bits)
      val smsi = (p.p.withImsic && p.p.withSupervisor) generate Bits(p.p.imsicInterrupts - 1 bits)
    }
  }

  def bind(ctrl: InterruptCtrlFiber) = priv match {
    case Some(priv) => new Area {
      val pp = priv.plugin
      val intIdBase = pp.hartIds(0) * (1 + pp.p.withSupervisor.toInt)
      ctrl.mapDownInterrupt(intIdBase, priv.mei)
      if(pp.p.withSupervisor) ctrl.mapDownInterrupt(intIdBase + 1, priv.sei)
    }
  }


  def bind(clint: TilelinkClintFiber): Unit = priv match {
    case Some(priv) => new Area {
      val pp = priv.plugin
      val up = clint.createPort(pp.hartIds(0))
      priv.mti << up.mti
      priv.msi << up.msi
      DataCc(up.stoptime, priv.stoptime.clockDomain(RegNext(priv.stoptime)))(False)
      val time = priv.plugin.p.withRdTime generate new Area{
        val timeBuffer = priv.rdtime.clockDomain(Reg(UInt(64 bits)))
        DataCc(timeBuffer, clint.time)(U(0, 64 bits))
        priv.rdtime := timeBuffer
      }
    }
  }

  def bind(aplic: TilelinkAPlicFiber) = priv match {
    case Some(priv) => new Area {
      val pp = priv.plugin
      val intIdBase = pp.hartIds(0)
      aplic.domainParam.isMDomain match {
        case true => aplic.mapDownInterrupt(intIdBase, priv.mei)
        case false => aplic.mapDownInterrupt(intIdBase, priv.sei)
      }
    }
  }

  def bind(msi: TilelinkImsicTriggerFiber, mode: Int) = priv match {
    case Some(priv) => new Area {
      val pp = priv.plugin
      val intIdBase = pp.hartIds(0)
      val intNum = pp.p.imsicInterrupts

      mode match {
        case PrivilegeMode.M => priv.mmsi := msi.addImsicFileinfo(ImsicFileInfo(intIdBase, 1 until intNum))
        case PrivilegeMode.S => priv.smsi := msi.addImsicFileinfo(ImsicFileInfo(intIdBase, 1 until intNum))
      }
    }
  }

  // Add the plugins to bridge the CPU toward Tilelink
  plugins.foreach {
    case p: FetchCachelessPlugin => plugins += new FetchCachelessTileLinkPlugin(iBus)
    case p: FetchL1Plugin => plugins += new FetchL1TileLinkPlugin(iBus)
    case p: LsuCachelessPlugin => plugins += new LsuCachelessTileLinkPlugin(dBus)
    case p: LsuPlugin => plugins += new LsuTileLinkPlugin(dBus)
    case p: LsuL1Plugin => plugins += new LsuL1TileLinkPlugin(lsuL1Bus)
    case _ =>
  }


  val logic = Fiber setup new Area{
    val core = VexiiRiscv(plugins)
    Fiber.awaitBuild()
    def getRegion(node : Node) = MemoryConnection.getMemoryTransfers(node).asInstanceOf[ArrayBuffer[PmaRegion]]
    plugins.foreach {
      case p: FetchCachelessPlugin => p.regions.load(getRegion(iBus))
      case p: FetchL1Plugin => p.regions.load(getRegion(iBus))
      case p: LsuCachelessPlugin => p.regions.load(getRegion(dBus))
      case p: LsuPlugin => p.ioRegions.load(getRegion(dBus))
      case p: LsuL1Plugin => p.regions.load(getRegion(lsuL1Bus))
      case _ =>
    }

    //Connect stuff
    plugins.foreach {
      case p: PrivilegedPlugin => {
        val hart = p.logic.harts(0)
        hart.int.m.timer := priv.get.mti.flag
        hart.int.m.software := priv.get.msi.flag
        hart.int.m.external := priv.get.mei.flag
        priv.get.stoptime := p.p.withDebug.mux(hart.debug.stoptime, False)
        if (p.p.withSupervisor) hart.int.s.external := priv.get.sei.flag
        if (p.p.withRdTime) p.logic.rdtime := priv.get.rdtime
        if (p.p.withImsic) {
          hart.m.imsic.triggers := priv.get.mmsi
          if (p.p.withSupervisor) hart.s.imsic.triggers := priv.get.smsi
        }
      }
      case p: vexiiriscv.execute.cfu.CfuPlugin => {
        cfuBus.node << p.logic.bus
      }
      case p: vexiiriscv.execute.cxu.CxuPlugin => {
        cxuBus.mcx_selector := p.logic.mcx_selector

        // Initialize default values to prevent latches
        p.logic.cxuBus.cmd.ready := False
        p.logic.cxuBus.rsp.valid := False
        p.logic.cxuBus.rsp.payload.response_id := 0
        for(i <- p.logic.cxuBus.rsp.payload.outputs.indices) {
          p.logic.cxuBus.rsp.payload.outputs(i) := 0
        }
        if(p.p.CXU_WITH_STATUS) {
          p.logic.cxuBus.rsp.payload.status := 0
        }
        if(p.p.CXU_FEATURE_LEVEL >= 2) {
          p.logic.cxuBus.rsp.payload.ready := False
        }

        // Connect each bus
        for ((busArea, i) <- cxuBus.buses.zipWithIndex) {
          val isSelected = cxuBus.mcx_selector === U(i, cxuBus.mcx_selector.getWidth bits)
          val bus = busArea.node

          // Command path
          bus.cmd.valid := p.logic.cxuBus.cmd.valid && isSelected
          bus.cmd.payload := p.logic.cxuBus.cmd.payload
          when(isSelected) {
            p.logic.cxuBus.cmd.ready := bus.cmd.ready
          }

          // Response path
          when(bus.rsp.valid && isSelected) {
            p.logic.cxuBus.rsp.valid := True
            p.logic.cxuBus.rsp.payload := bus.rsp.payload
          }
          bus.rsp.ready := p.logic.cxuBus.rsp.ready && isSelected
        }
      }
      case _ =>
    }
  }

  override def getXlen(): Int = logic.core.database(Riscv.XLEN)
  override def getFlen(): Int = logic.core.database(Riscv.FLEN)
  override def getHartId(): Int = ???
  override def getIntMachineTimer(): Bool = ???
  override def getIntMachineSoftware(): Bool = ???
  override def getIntMachineExternal(): Bool = ???
  override def getIntSupervisorExternal(): Bool = ???
  override def getDebugBus(): DebugHartBus = plugins.collectFirst {case p : PrivilegedPlugin => p.logic.harts(0).debug.bus}.get
}
