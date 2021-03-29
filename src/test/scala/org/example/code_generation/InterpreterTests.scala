package org.example.code_generation

import org.example.code_generation.proc.Command
import org.example.code_generation.proc.ExecutorState
import org.example.code_generation.proc.Interpreter
import org.example.code_generation.proc.MemoryState
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class InterpreterTests extends AnyFunSuite with Matchers {

  println(Interpreter.stringExpression)

  def execute(commandsLines: String): MemoryState = {
    val commands = commandsLines.linesIterator.map(Command.parse).toArray
    val initialState = ExecutorState.empty(commands, 8)
    Interpreter.execute(initialState).memoryState
  }

  def areSubset(testName: String, commands: String, expectedRegisters: Map[Int, Int], expectedMemory: Map[Int, Int] = Map.empty): Unit = {
    test(testName){
      val resultMemory = execute(commands)
      println("Registers: " + resultMemory.registers)
      println("Memory: " + resultMemory.memory)
      resultMemory.registers should contain allElementsOf expectedRegisters
      resultMemory.memory should contain allElementsOf expectedMemory
    }
  }

  areSubset(
    "simple load command",
    "ldc 0 1",
    Map(0 -> 1)
  )

  areSubset(
    "simple store command",
    """ldc 0 5
      |st 2 0""".stripMargin,
    Map.empty,
    Map(2 -> 5)
  )

  areSubset(
    "simple move command",
    """ldc 0 6
      |mv 2 0""".stripMargin,
    Map(2 -> 6)
  )

  areSubset(
    "simple sum command",
    """ldc 0 1
      |ldc 1 2
      |add 1 0""".stripMargin,
    Map(0 -> 1, 1 -> 3)
  )

  areSubset(
    "simple multiply command",
    """ldc 0 2
      |ldc 1 3
      |mul 1 0""".stripMargin,
    Map(0 -> 2, 1 -> 6)
  )

  areSubset(
    "simple subtract command",
    """ldc 0 5
      |ldc 2 4
      |sub 0 2""".stripMargin,
    Map(0 -> 1, 2 -> 4)
  )

  areSubset(
    "simple load from memory command",
    """ldc 0 5
      |st 4 0
      |ld 2 4""".stripMargin,
    Map(0 -> 5, 2 -> 5),
    Map(4 -> 5)
  )

  areSubset(
    "simple jump command",
    """ldc 0 0
      |jmp 3
      |ldc 0 1""".stripMargin,
    Map(0 -> 0)
  )

  areSubset(
    "simple compare should be equal",
    """ldc 0 1
      |ldc 1 1
      |cmp 1 0""".stripMargin,
    Map(0 -> 1, 1 -> 0)
  )

  areSubset(
    "simple compare should be smaller",
    """ldc 0 1
      |ldc 1 0
      |cmp 1 0""".stripMargin,
    Map(0 -> 1, 1 -> -1)
  )

  areSubset(
    "simple compare should be greater",
    """ldc 0 1
      |ldc 1 2
      |cmp 1 0""".stripMargin,
    Map(0 -> 1, 1 -> 1)
  )

  areSubset(
    "7 factorial",
    """ldc 0 7
      |ldc 1 1
      |ldc 2 1
      |mul 1 0
      |sub 0 2
      |ldc 3 0
      |cmp 3 0
      |jmpLt 3 3
      |mv 0 1
      |""".stripMargin,
    expectedRegisters = Map(0 -> 5040)
  )

  areSubset(
    "9th fibonacci number",
    """ldc 0 0
      |ldc 1 1
      |ldc 2 9
      |ldc 3 1
      |ldc 4 0
      |mv 5 0
      |mv 0 1
      |add 1 5
      |sub 2 3
      |ldc 6 1
      |cmp 6 2
      |jmpLt 5 6""".stripMargin,
    expectedRegisters = Map(0 -> 21, 1 -> 34)
  )

}
