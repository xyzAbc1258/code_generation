package org.example.code_generation.proc

import bshapeless.MGenerator
import bshapeless.NoLoops
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
    override type Repr = Finish.type :+: JmpIf :+: Jmp :+: Load :+: LoadConst :+: Move :+: OpCommand :+: Store :+: CNil

    override def from(r: Repr): Command = Coproduct.unsafeGet(r).asInstanceOf[Command]

    override def to(t: Command): Repr = t match {
      case Finish => Coproduct[Repr](Finish)
      case command: OpCommand => Coproduct[Repr](command)
      case command: Load => Coproduct[Repr](command)
      case command: LoadConst => Coproduct[Repr](command)
      case command: Store => Coproduct[Repr](command)
      case command: Move => Coproduct[Repr](command)
      case command: Jmp => Coproduct[Repr](command)
      case command: JmpIf => Coproduct[Repr](command)
    }
  }

  def execute(e: ExecutorState): ExecutorState = allExecute(e)

  private def allExecute(e: ExecutorState): ExecutorState with Final = {
    val f = MGenerator.raw[
      Nat._6,
      ((ExecutorState with Result) => ExecutorState with Final)::
        ObjectFuncProvider[Finish.type]::
        ObjectFuncProvider[MemoryStateApi] ::
        ObjectFuncProvider[Load] ::
        ObjectFuncProvider[Store] ::
        ObjectFuncProvider[Move] ::
        ObjectFuncProvider[LoadConst] ::
        ObjectFuncProvider[BinOp] ::
        ObjectFuncProvider[IntOp] ::
        ObjectFuncProvider[Jmp] ::
        ObjectFuncProvider[JmpIf] ::
        ObjectFuncProvider[CmpWhich] ::
        (ExecutorState => (Int with LineNumber) => (Boolean with Result) => (ExecutorState with Result)) ::
        ObjectFuncProvider[ExecutorApi] ::
        HNil,
      genericCommand.Repr,
      ExecutorState => (ExecutorState with Final),
      NoLoops
    ](
      (allExecute _) ::
        ObjectFuncProvider::
        (ObjectFuncProvider ::
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
            if (jump) x.jumpTo(line)
            else x.nextWithStateI(x.memoryState).tag[Result]
            ) ::
          ObjectFuncProvider ::
          HNil),
      genericCommand.to(e.currentInstruction)
    )
    f(e)
  }

  def jmpif(
    state: ExecutorApi)(
    line: Int with LineNumber)(
    ifJump: Boolean with Result
  ): ExecutorApi with Result = {
    if(ifJump) state.jumpTo(line)
    else state.nextLineWithState(state.memoryState.tag[Result])
  }
}
