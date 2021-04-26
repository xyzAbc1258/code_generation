package org.example.code_generation.proc

import bshapeless.MGenerator
import bshapeless.ObjectFuncProvider
import bshapeless.Options
import org.example.code_generation.examples5.Degeneric2
import org.example.code_generation.proc.Semantics.Tag
import shapeless.:+:
import shapeless.::
import shapeless.CNil
import shapeless.Coproduct
import shapeless.Generic
import shapeless.HNil
import shapeless.Nat

import scala.annotation.tailrec

object Interpreter {

  val genericCommand = new Generic[Command] {
    override type Repr = JmpIf :+: Jmp :+: Load :+: LoadConst :+: MoveReg :+: OpCommand :+: Store :+: CNil

    override def from(r: Repr): Command = Coproduct.unsafeGet(r).asInstanceOf[Command]

    override def to(t: Command): Repr = t match {
      case command: OpCommand => Coproduct[Repr](command)
      case command: Load => Coproduct[Repr](command)
      case command: LoadConst => Coproduct[Repr](command)
      case command: Store => Coproduct[Repr](command)
      case command: MoveReg => Coproduct[Repr](command)
      case command: Jmp => Coproduct[Repr](command)
      case command: JmpIf => Coproduct[Repr](command)
    }
  }

  private type RegRetrieve[RegAttr, ResultAttr] = MemoryState => (Int with RegAttr) => (Int with ResultAttr)

  private val rrType = Degeneric2[(RegSrc, Result) :: (RegOp1, Operand1) :: (RegOp2, Operand2) :: HNil, RegRetrieve]

  private type Ctx = (MemoryState => ((Int with Result, Int with RegDst)) => (MemoryState with Result)) ::
    (MemoryState => ((Int with Result, Int with MemDst)) => (MemoryState with Result)) ::
    (MemoryState => (Int with MemSrc) => (Int with Result)) ::
    rrType.Out ::
    ObjectFuncProvider[Load] ::
    ObjectFuncProvider[Store] ::
    ObjectFuncProvider[MoveReg] ::
    ObjectFuncProvider[LoadConst] ::
    ObjectFuncProvider[OpCommandAbs] ::
    ObjectFuncProvider[IntOp] ::
    ObjectFuncProvider[Jmp] ::
    ObjectFuncProvider[JmpIf] ::
    ObjectFuncProvider[CmpWhich] ::
    (ExecutorState => (Int with LineNumber) => (Boolean with Result) => (ExecutorState with Result)) ::
    ObjectFuncProvider[ExecutorApi] ::
    HNil


  private val ctxValue: Ctx =
    (((x: MemoryState) => (y: (Int with Result, Int with RegDst)) => x.withReg(y._2, y._1).tag[Result]) ::
      ((x: MemoryState) => (y: (Int with Result, Int with MemDst)) => x.withMemory(y._2, y._1).tag[Result]) ::
      ((x: MemoryState) => (y: Int with MemSrc) => x.getMemory(y).tag[Result]) ::
      ((x: MemoryState) => (y: Int with RegSrc) => x.getReg(y).tag[Result]) ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ((x: ExecutorState) => (line: Int with LineNumber) => (jump: Boolean with Result) =>
        if (jump) x.jumpTo(line).tag[Result]
        else x.nextWithStateI(x.memoryState).tag[Result]
        ) ::
      ObjectFuncProvider ::
      HNil).asInstanceOf[Ctx]


  private val generator = { x: genericCommand.Repr =>
    MGenerator.raw[
      Nat._5,
      Ctx,
      genericCommand.Repr,
      ExecutorState => (ExecutorState with Result),
      Options
    ]((((x: MemoryState) => (y: (Int with Result, Int with RegDst)) => x.withReg(y._2, y._1).tag[Result]) ::
      ((x: MemoryState) => (y: (Int with Result, Int with MemDst)) => x.withMemory(y._2, y._1).tag[Result]) ::
      ((x: MemoryState) => (y: Int with MemSrc) => x.getMemory(y).tag[Result]) ::
      ((x: MemoryState) => (y: Int with RegSrc) => x.getReg(y).tag[Result with Operand1 with Operand2]) ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ObjectFuncProvider ::
      ((x: ExecutorState) => (line: Int with LineNumber) => (jump: Boolean with Result) =>
        if (jump) x.jumpTo(line).tag[Result]
        else x.nextWithStateI(x.memoryState).tag[Result]
        ) ::
      ObjectFuncProvider ::
      HNil).asInstanceOf[Ctx], x)
  }

  def stringExpression: String = {
    /*generator.stringify(
      "set_register" ::
        "set_memory" ::
        "get_memory" ::
        "get_register" ::
        "" :: "" :: "" :: "" :: "" :: "" :: "" :: "" :: "" ::
        "conditional_jump" ::
        "" ::
        HNil, "command")*/ ""
  }

  @tailrec
  final def execute(x: ExecutorState): ExecutorState = {
    if (x.finished) x
    else {
      val next = generator(genericCommand.to(x.currentInstruction))(x)
      execute(next)
    }
  }

}
