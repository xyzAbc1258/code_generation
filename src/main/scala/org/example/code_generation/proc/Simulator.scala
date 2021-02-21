package org.example.code_generation.proc

import bshapeless.{MGenerator, NamedStruct}
import org.example.code_generation.examples5.Generator.{Mode, NoRepeatAppFunction, NoSubtyping, OnlyOne, OnlyOneNoRepeat}
import org.example.code_generation.examples5.{Degeneric2, Expr, Generator, Reachable}
import org.example.code_generation.proc.Semantics.Tag
import shapeless._

import scala.annotation.tailrec

object Simulator {

  def gen: ExecutorState => ExecutorState = {
    type RegRetrieve[RegAttr, ResultAttr] = MemoryState => (Int with RegAttr) => (Int with ResultAttr)

    val rrType = Degeneric2[(RegSrc, Result) :: (RegOp1, Operand1) :: (RegOp2, Operand2) :: HNil, RegRetrieve]

    type Ctx = (MemoryState => ((Int with Result, Int with RegDst)) => (MemoryState with Result)) ::
      (MemoryState => ((Int with Result, Int with MemDst)) => (MemoryState with Result)) ::
      (MemoryState => (Int with MemSrc) => (Int with Result)) ::
      rrType.Out ::
      (Load => (Int with MemSrc)) ::
      (Load => (Int with RegDst)) ::
      (Store => (Int with RegSrc)) ::
      (Store => (Int with MemDst)) ::
      (MoveReg => (Int with RegSrc)) ::
      (MoveReg => (Int with RegDst)) ::
      (LoadConst => (Int with Result)) ::
      (LoadConst => (Int with RegDst)) ::
      (OpCommand => IntOp) ::
      (OpCommand => (Int with RegOp1 with RegDst)) ::
      (OpCommand => (Int with RegOp2)) ::
      (IntOp => ((Int with Operand1, Int with Operand2)) => Int with Result) ::
      (Jmp => (Int with LineNumber)) ::
      (ExecutorState => JmpIf => (ExecutorState with Result)) ::
      (ExecutorState => MemoryState) ::
      (ExecutorState => (MemoryState with Result) => (ExecutorState with Result)) ::
      (ExecutorState => (Int with LineNumber) => (ExecutorState with Result)) ::
      HNil


    val gen = new Generic[Command] {
      override type Repr = JmpIf :+: Jmp :+: Load :+: LoadConst :+: MoveReg :+: OpCommand :+: Store :+: CNil

      override def to(t: Command): Repr = t match {
        case command: OpCommand => Coproduct[Repr](command)
        case command: Load => Coproduct[Repr](command)
        case command: LoadConst => Coproduct[Repr](command)
        case command: Store => Coproduct[Repr](command)
        case command: MoveReg => Coproduct[Repr](command)
        case command: Jmp => Coproduct[Repr](command)
        case command: JmpIf => Coproduct[Repr](command)
      }

      override def from(r: Repr): Command = Coproduct.unsafeGet(r).asInstanceOf[Command]
    }

    val es2 = MGenerator[
      Nat._5,
      Ctx,
      gen.Repr,
      ExecutorState => (ExecutorState with Result)
    ]
    /*
        for (e <- Set(es2.expressions:_*).toList.sortBy(_.size).headOption) {
          println(e.stringify(
            "storeReg" ::
              "storeMem" ::
              "getMem" ::
              "getReg" ::
              "load_memSrc" ::
              "load_regDst" ::
              "store_regSrc" ::
              "store_memDst" ::
              "move_regSrc" ::
              "move_regDst" ::
              "load_value" ::
              "load_regDst" ::
              "op_intOp" ::
              "op_operand1_and_regDst" ::
              "op_operand2" ::
              "apply_op" ::
              "jmp_line_number" ::
              "conditional_jmp" ::
              "get_state" ::
              "next_line_with_state" ::
              "jump_to" ::
              HNil,
            "command"
          ))
        }*/

    val ctxValue: Ctx =
      (((x: MemoryState) => (y: (Int with Result, Int with RegDst)) => x.withReg(y._2, y._1).tag[Result]) ::
      ((x: MemoryState) => (y: (Int with Result, Int with MemDst)) => x.withMemory(y._2, y._1).tag[Result]) ::
      ((x: MemoryState) => (y: Int with MemSrc) => x.getMemory(y).tag) ::
      ((x: MemoryState) => (y: Int with RegSrc) => x.getReg(y).tag) ::
      ((_: Load).memoryLocation) ::
      ((_: Load).register) ::
      ((_: Store).register) ::
      ((_: Store).memoryLocation) ::
      ((_: MoveReg).regSrc) ::
      ((_: MoveReg).regDest) ::
      ((_: LoadConst).value) ::
      ((_: LoadConst).register) ::
      ((_: OpCommand).op) ::
      ((_: OpCommand).r1Ext) ::
      ((_: OpCommand).r2Ext) ::
      ((x: IntOp) => (v: (Int with Operand1, Int with Operand2)) => x.execute(v._1, v._2)) ::
      ((_: Jmp).line.tag[LineNumber]) ::
      ((x: ExecutorState) => (j: JmpIf) =>
        if (j.which.isOkay(x.memoryState.getReg(j.reg)))
          x.jumpTo(j.lineNumber).tag[Result]
        else x.nextWithState(x.memoryState).tag[Result]) ::
      ((_: ExecutorState).memoryState) ::
      ((x: ExecutorState) => (ns: MemoryState with Result) => x.nextWithState(ns).tag[Result]) ::
      ((x: ExecutorState) => (ln: Int with LineNumber) => x.jumpTo(ln).tag[Result]) ::
      HNil).asInstanceOf[Ctx]


    val first = es2.expressions.minBy(_.size)

    @tailrec
    def f(x: ExecutorState): ExecutorState = {
      if (x.finished) x
      else {
        val next = first(ctxValue, gen.to(x.currentInstruction))(x)
        f(next)
      }
    }

    f
  }

  def main(args: Array[String]): Unit = {
    val inp = inputSet()
    val state = ExecutorState.empty(inp.toArray,8)
    val r = gen.apply(state)
    println(s"Result memory: ${r.memoryState}")
    println(s"Result: ${r.memoryState.getReg(0)}")
  }

  @tailrec
  def inputSet(cs: Seq[Command] = Nil): Seq[Command] = {
    val l = io.StdIn.readLine()
    if (l == "execute") cs
    else inputSet(cs :+ parse(l))
  }

  def parse(line: String): Command = {
    implicit def p[T <: Semantics](s: String): Int with T = java.lang.Integer.parseInt(s).tag[T]

    line match {
      case s"ld $memSrc $regDst" => Load(memSrc, regDst) //load
      case s"ldc $regDst $const" => LoadConst(regDst, const) //load const
      case s"st $regSrc $memDest" => Store(regSrc, memDest) //store
      case s"mv $regSrc $regDst" => MoveReg(regSrc, regDst) //move
      case s"add $reg1 $reg2" => Add(reg1, reg2) //add
      case s"sub $reg1 $reg2" => Subtract(reg1, reg2) //sub
      case s"mul $reg1 $reg2" => Mul(reg1, reg2) //multiply
      case s"jmp $line" => Jmp(line) // jmp
      case s"jmpEq $line $reg" => JmpIf(line, reg, Eq) // jmp if zero
      case s"jmpLt $line $reg" => JmpIf(line, reg, Lt) //jmp if negative
      case s"jmpGt $line $reg" => JmpIf(line, reg, Gt) //jmp if positive
      case s"cmp $r1 $r2" => Cmp(r1, r2) // compares two registers and stores result in first
    }
  }

  /* 7 silnia
ldc 0 6
ldc 1 1
ldc 2 1
mul 1 0
sub 0 2
ldc 3 0
cmp 3 0
jmpLt 3 3
mv 1 0
execute
   */
}
