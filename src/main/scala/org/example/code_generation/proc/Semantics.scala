package org.example.code_generation.proc

sealed trait Semantics

object Semantics {
  implicit class Tag[T](t: T) {
    def tag[S <: Semantics]: T with S = t.asInstanceOf[T with S]
  }
}

trait OpSemantics extends Semantics

trait Operand1 extends OpSemantics
trait Operand2 extends OpSemantics
trait Result extends OpSemantics

trait MemSrc extends Semantics
trait MemDst extends Semantics

trait RegOp1 extends Semantics
trait RegOp2 extends Semantics

trait RegSrc extends Semantics
trait RegDst extends Semantics

trait LineNumber extends Semantics