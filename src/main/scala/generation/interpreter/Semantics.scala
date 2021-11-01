package generation.interpreter

object Semantics {
  implicit class Tag[T](t: T) {
    def tag[S <: Semantics]: T with S = t.asInstanceOf[T with S]
  }
}

sealed trait Semantics

trait OpSemantics extends Semantics

trait Operand1 extends OpSemantics
trait Operand2 extends OpSemantics
trait Result extends OpSemantics

trait Final extends Semantics

trait MemSrc extends Semantics
trait MemDst extends Semantics

trait RegOp1 extends Semantics
trait RegOp2 extends Semantics

trait RegSrc extends Semantics
trait RegDst extends Semantics

trait LineNumber extends Semantics