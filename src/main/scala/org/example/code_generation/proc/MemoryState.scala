package org.example.code_generation.proc

case class MemoryState(memory: Map[Int, Int], registers: Map[Int, Int], maxRegister: Int) {

  def withMemory(loc: Int, value: Int): MemoryState =
    copy(memory = memory.updated(loc, value))

  def withReg(reg: Int, value: Int): MemoryState = {
    assert(reg < maxRegister)
    copy(registers = registers.updated(reg, value))
  }

  def getMemory(loc: Int): Int = memory.getOrElse(loc, 0)

  def getReg(reg: Int): Int = {
    assert(reg < maxRegister)
    registers.getOrElse(reg, 0)
  }
}

object MemoryState {
  def empty(maxRegisters: Int): MemoryState = MemoryState(Map.empty, Map.empty, maxRegisters)
}