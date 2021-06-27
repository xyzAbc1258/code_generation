package org.example.code_generation.proc

import bshapeless.MGenerator
import bshapeless.NoLoops
import bshapeless.ObjectFuncProvider
import bshapeless.Options
import org.example.code_generation.examples5.Degeneric2
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
      HNil


    val gen = new Generic[Command] {
      override type Repr = JmpIf :+: Jmp :+: Load :+: LoadConst :+: Move :+: OpCommand :+: Store :+: CNil

      override def to(t: Command): Repr = t match {
        case command: OpCommand => Coproduct[Repr](command)
        case command: Load => Coproduct[Repr](command)
        case command: LoadConst => Coproduct[Repr](command)
        case command: Store => Coproduct[Repr](command)
        case command: Move => Coproduct[Repr](command)
        case command: Jmp => Coproduct[Repr](command)
        case command: JmpIf => Coproduct[Repr](command)
      }

      override def from(r: Repr): Command = Coproduct.unsafeGet(r).asInstanceOf[Command]
    }

    val es2 = MGenerator.applyL[
      Nat._5,
      Nat._5,
      Ctx,
      gen.Repr,
      ExecutorState => (ExecutorState with Result),
      Options
    ]

    for (e <- Set(es2.expressions: _*).toList.sortBy(_.size)) {
      println(e.stringify(
        "storeReg" ::
          "storeMem" ::
          "getMem" ::
          "getReg" ::
          "" :: "" :: "" :: "" :: "" ::
          "" ::
          "" :: "" :: "" ::
          "conditional_jmp" ::
          "" ::
          HNil,
        "command"
      ))
    }

    val ctxValue: Ctx =
      (((x: MemoryState) => (y: (Int with Result, Int with RegDst)) => x.withRegister(y._2)(y._1).tag[Result]) ::
        ((x: MemoryState) => (y: (Int with Result, Int with MemDst)) => x.withMemory(y._2)(y._1).tag[Result]) ::
        ((x: MemoryState) => (y: Int with MemSrc) => x.getMemory(y)) ::
        ((x: MemoryState) => (y: Int with RegSrc) => x.getRegister(y)) ::
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
    {
      type RegRetrieve[RegAttr, ResultAttr] = MemoryState => (Int with RegAttr) => (Int with ResultAttr)

      val rrType = Degeneric2[(RegSrc, Result) :: (RegOp1, Operand1) :: (RegOp2, Operand2) :: HNil, RegRetrieve]

      val ss = MGenerator.RuntimeMacroImpl.generateStrings[
        Nat._1,
        Nat._5,
        (MemoryState => ((Int with Result, Int with RegDst)) => (MemoryState with Result)) ::
          (MemoryState => ((Int with Result, Int with MemDst)) => (MemoryState with Result)) ::
          (MemoryState => (Int with MemSrc) => (Int with Result)) ::
          ((MemoryState => (Int with RegSrc) => (Int with Result)
            ) with (MemoryState => (Int with RegOp1) => (Int with Operand1)
            ) with (MemoryState => (Int with RegOp2) => (Int with Operand2))) ::
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
        JmpIf :+: Jmp :+: Load :+: LoadConst :+: Move :+: OpCommand :+: Store :+: CNil,
        ExecutorState => (ExecutorState with Result),
        Options
      ]

      println(ss)
      sys.exit(1)
    }

    val inp = inputSet()
    val state = ExecutorState.empty(inp.toArray, 8)
    val r = gen.apply(state)
    println(s"Result memory: ${r.memoryState}")
    println(s"Result: ${r.memoryState.getRegister(0.tag[RegSrc])}")
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
      case s"mv $regSrc $regDst" => Move(regSrc, regDst) //move
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
