package org.example.code_generation.proc

import Semantics._


sealed trait IntOp {

  protected implicit def toResult(s: Int): Int with Result = s.tag[Result]

  def execute(op1: Int with Operand1)(op2: Int with Operand2): Int with Result
}

case object AddOp extends IntOp {
  override def execute(op1: Int with Operand1)(op2: Int with Operand2): Int with Result = op1 + op2
}

case object SubOp extends IntOp {
  override def execute(op1: Int with Operand1)(op2: Int with Operand2): Int with Result = op1 - op2
}

case object MulOp extends IntOp {
  override def execute(op1: Int with Operand1)(op2: Int with Operand2): Int with Result = op1 * op2
}

case object CmpOp extends IntOp {
  override def execute(op1: Int with Operand1)(op2: Int with Operand2): Int with Result =
    Ordering[Int].compare(op1, op2).tag[Result]
}

sealed trait Command
sealed trait OpCommandAbs extends Command {
  def r1Ext: Int with RegOp1 with RegDst
  def r2Ext: Int with RegOp2
  def op: IntOp
}
sealed abstract class OpCommand(val op: IntOp) extends OpCommandAbs {
  val r1: Int
  val r2: Int

  def r1Ext: Int with RegOp1 with RegDst = r1.tag
  def r2Ext: Int with RegOp2 = r2.tag
}

case class Load(memoryLocation: Int with MemSrc, register: Int with RegDst) extends Command

case class LoadConst(register: Int with RegDst, value: Int with Result) extends Command

case class Store(register: Int with RegSrc, memoryLocation: Int with MemDst) extends Command

case class MoveReg(regSrc: Int with RegSrc, regDest: Int with RegDst) extends Command

case class Jmp(line: Int with LineNumber) extends Command

case class Add(r1: Int, r2: Int) extends OpCommand(AddOp) //result in r1

case class Subtract(r1: Int, r2: Int) extends OpCommand(SubOp)

case class Mul(r1: Int, r2: Int) extends OpCommand(MulOp)

case class Cmp(r1: Int, r2: Int) extends OpCommand(CmpOp)

trait CmpWhich {
  def isOkay(compareValue: Int with Result): Boolean with Result
}

case object Gt extends CmpWhich {
  override def isOkay(compareValue: Int with Result): Boolean with Result = (compareValue > 0).tag
}

case object Lt extends CmpWhich {
  override def isOkay(compareValue: Int with Result): Boolean with Result = (compareValue < 0).tag
}

case object Eq extends CmpWhich {
  override def isOkay(compareValue: Int with Result): Boolean with Result = (compareValue == 0).tag
}

case class JmpIf(lineNumber: Int with LineNumber, reg: Int with RegSrc, which: CmpWhich) extends Command

object Command {

  def parse(line: String): Command = {
    implicit def p[T <: Semantics](s: String): Int with T = java.lang.Integer.parseInt(s).tag[T]

    line match {
      case s"ld $regDst $memSrc" => Load(memSrc, regDst) //load
      case s"ldc $regDst $const" => LoadConst(regDst, const) //load const
      case s"st $memDest $regSrc" => Store(regSrc, memDest) //store
      case s"mv $regDst $regSrc" => MoveReg(regSrc, regDst) //move
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

}