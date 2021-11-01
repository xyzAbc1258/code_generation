#Mechanism for automated code generation in Scala.

##Consists of two parts:
###- generator based on macros - generation.MGenerator in project macros
###- generator based on implicits - generation.implicit.Generator

##There are two examples of usage:
### - generated interpreter of simple assembler language - generation.interpreter packet
### - finding solution of maze using types - generation.maze.MazeSolver