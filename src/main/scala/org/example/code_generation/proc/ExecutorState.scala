package org.example.code_generation.proc

case class ExecutorState(initialInstructionSet: Array[Command], memoryState: MemoryState, currentInstrIndex: Int){

  def currentInstruction: Command = initialInstructionSet(currentInstrIndex)

  def jumpTo(index: Int): ExecutorState = copy(currentInstrIndex = index)

  def nextWithState(newState: MemoryState): ExecutorState =
    copy(memoryState = newState, currentInstrIndex = currentInstrIndex + 1)

  def finished: Boolean = currentInstrIndex >= initialInstructionSet.length
}

object ExecutorState {
  def empty(instructions: Array[Command], registers: Int): ExecutorState =
    new ExecutorState(instructions, MemoryState.empty(registers), 0)
}