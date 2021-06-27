package org.example.code_generation.proc

import org.example.code_generation.proc.Semantics.Tag

trait MemoryStateApi {

  protected def withMemImpl(loc: Int, value: Int): MemoryState

  def withMemory(
    loc: Int with MemDst)(
    value: Int with Result
  ): MemoryState with Result = withMemImpl(loc, value).tag[Result]

  protected def withRegImpl(reg: Int, value: Int): MemoryState

  def withRegister(
    reg: Int with RegDst)(
    value: Int with Result
  ): MemoryState with Result = withRegImpl(reg, value).tag[Result]

  protected def getMemoryImpl(loc: Int): Int

  def getMemory(loc: Int with MemSrc): Int with Result = getMemoryImpl(loc).tag[Result]

  protected def getRegImpl(reg: Int): Int

  def getRegister: ((Int with RegSrc) => (Int with Result)) with
    ((Int with RegOp1) => (Int with Operand1)) with
    ((Int with RegOp2) => (Int with Operand2)) = (x: Int) => getRegImpl(x).tag[Result with Operand1 with Operand2]
}

case class MemoryState(
  memory: Map[Int, Int],
  registers: Map[Int, Int],
  maxRegister: Int
) extends MemoryStateApi {

  protected def withMemImpl(loc: Int, value: Int): MemoryState =
    copy(memory = memory.updated(loc, value))

  protected def withRegImpl(reg: Int, value: Int): MemoryState = {
    assert(reg < maxRegister)
    copy(registers = registers.updated(reg, value))
  }

  protected def getMemoryImpl(loc: Int): Int = memory.getOrElse(loc, 0)

  protected def getRegImpl(reg: Int): Int = {
    assert(reg < maxRegister)
    registers.getOrElse(reg, 0)
  }
}

object MemoryState {
  def empty(maxRegisters: Int): MemoryState = MemoryState(Map.empty, Map.empty, maxRegisters)
}