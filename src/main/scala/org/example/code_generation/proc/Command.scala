package org.example.code_generation.proc

import Semantics._


sealed trait IntOp {

  implicit def toResult(s: Int): Int with Result = s.tag[Result]

  def execute(op1: Int with Operand1, op2: Int with Operand2): Int with Result
}

case object AddOp extends IntOp {
  override def execute(op1: Int with Operand1, op2: Int with Operand2): Int with Result = op1 + op2
}

case object SubOp extends IntOp {
  override def execute(op1: Int with Operand1, op2: Int with Operand2): Int with Result = op1 - op2
}

case object MulOp extends IntOp {
  override def execute(op1: Int with Operand1, op2: Int with Operand2): Int with Result = op1 * op2
}

case object CmpOp extends IntOp {
  override def execute(op1: Int with Operand1, op2: Int with Operand2): Int with Result =
    Ordering[Int].compare(op1, op2).tag[Result]
}

sealed trait Command

sealed abstract class OpCommand(val op: IntOp) extends Command {
  val r1: Int
  val r2: Int

  def r1Ext: Int with RegOp1 with RegDst = r1.tag
  def r2Ext: Int with RegOp2 = r2.tag
}

case class Load(memoryLocation: Int with MemSrc, register: Int with RegDst) extends Command

case class LoadConst(register: Int with RegDst, value: Int with Result) extends Command

case class Store(register: Int with RegSrc, memoryLocation: Int with MemDst) extends Command

case class MoveReg(regSrc: Int with RegSrc, regDest: Int with RegDst) extends Command

case class Jmp(line: Int) extends Command

case class Add(r1: Int, r2: Int) extends OpCommand(AddOp) //result in r1

case class Subtract(r1: Int, r2: Int) extends OpCommand(SubOp)

case class Mul(r1: Int, r2: Int) extends OpCommand(MulOp)

case class Cmp(r1: Int, r2: Int) extends OpCommand(CmpOp)

trait CmpWhich {
  def isOkay(compareValue: Int): Boolean
}

case object Gt extends CmpWhich {
  override def isOkay(compareValue: Int): Boolean = compareValue > 0
}

case object Lt extends CmpWhich {
  override def isOkay(compareValue: Int): Boolean = compareValue < 0
}

case object Eq extends CmpWhich {
  override def isOkay(compareValue: Int): Boolean = compareValue == 0
}

case class JmpIf(lineNumber: Int with LineNumber, reg: Int with RegSrc, which: CmpWhich) extends Command