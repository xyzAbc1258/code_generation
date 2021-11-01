package generation.interpreter

import generation.interpreter.Semantics.Tag

trait ExecutorApi {
  def memoryState: MemoryState
  def jumpTo(index: Int with LineNumber): ExecutorState with Result
  def nextLineWithState(newState: MemoryState with Result): ExecutorState with Result
}

case class ExecutorState(
  initialInstructionSet: Array[Command],
  memoryState: MemoryState,
  currentInstrIndex: Int) extends ExecutorApi {

  def currentInstruction: Command = if(finished) Finish else initialInstructionSet(currentInstrIndex)

  def jumpToI(index: Int): ExecutorState = copy(currentInstrIndex = index)

  def nextWithStateI(newState: MemoryState): ExecutorState =
    copy(memoryState = newState, currentInstrIndex = currentInstrIndex + 1)

  def finished: Boolean = currentInstrIndex >= initialInstructionSet.length

  override def jumpTo(index: Int with LineNumber): ExecutorState with Result =
    jumpToI(index.asInstanceOf[Int]).tag

  override def nextLineWithState(newState: MemoryState with Result): ExecutorState with Result =
    nextWithStateI(newState).tag
}

object ExecutorState {
  def empty(instructions: Array[Command], registers: Int): ExecutorState =
    new ExecutorState(instructions, MemoryState.empty(registers), 0)
}