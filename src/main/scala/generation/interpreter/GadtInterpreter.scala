package generation.interpreter

import generation.MGenerator
import generation.ObjectFuncProvider
import generation.Options
import shapeless.:+:
import shapeless.::
import shapeless.CNil
import shapeless.Coproduct.unsafeGet
import shapeless.Generic
import shapeless.HNil
import shapeless.Nat

object GadtInterpreter {

  trait Next

  implicit def asNext[T](t: T): T with Next = t.asInstanceOf[T with Next]

  trait Result

  trait First extends Next

  trait Second extends Next

  implicit class With[T](e: T) {
    def first: T with First = e.asInstanceOf[T with First]

    def second: T with Second = e.asInstanceOf[T with Second]

    def result: T with Result = e.asInstanceOf[T with Result]
  }

  //implicit def asResult[T](t: T): T with Result = t.asInstanceOf[T with Result]

  sealed trait Expr[T]

  case class IntConst(i: Int with Result) extends Expr[Int]

  case class StringConst(s: String with Result) extends Expr[String]

  case class BooleanConst(i: Int with Result) extends Expr[Boolean]

  sealed trait UnaryOp[T] extends Expr[T] {
    implicit def asResult[T](t: T): T with Result = t.asInstanceOf[T with Result]
  }

  sealed trait BinaryOp[T] extends Expr[T] {
    protected def asResult[T](t: T): T with Result = t.asInstanceOf[T with Result]
  }

  case class Add(a: Expr[Int] with First, b: Expr[Int] with Second) extends BinaryOp[Int] {
    def exec(a: Int with First)(b: Int with Second): Int with Result = asResult[Int](a + b)
  }

  case class Multiply(a: Expr[Int] with First, b: Expr[Int] with Second) extends BinaryOp[Int] {
    def exec(a: Int with First)(b: Int with Second): Int with Result = asResult[Int](a * b)
  }

  case class Abs(a: Expr[Int] with First) extends UnaryOp[Int] {
    def mod(t: Int with First): Int with Result = asResult[Int](t.abs)
  }

  case class Concat(a: Expr[String] with First, b: Expr[String] with Second) extends BinaryOp[String] {
    def exec(a: String with First)(b: String with Second): String with Result = asResult[String](a + b)
  }

  case class And(a: Expr[Boolean] with First, b: Expr[Boolean] with Second) extends BinaryOp[Boolean] {
    def exec(a: Boolean with First)(b: Boolean with Second): Boolean with Result = asResult[Boolean](a && b)
  }

  case class Or(a: Expr[Boolean] with First, b: Expr[Boolean] with Second) extends BinaryOp[Boolean] {
    def exec(a: Boolean with First)(b: Boolean with Second): Boolean with Result = asResult[Boolean](a || b)
  }

  def fixpoint[A, B](f: (A => B) => (A => B)): A => B = {
    def x(a: A): B = f(x)(a)

    x
  }

  val gen = Generic[Expr[_]]

  trait Interpreter {
    def interpretFirst[T](t: Expr[T] with First): T with First

    def interpretSecond[T](t: Expr[T] with Second): T with Second
  }

  def interpret[T](t: Expr[T]): T = {
    val interpreter = new Interpreter {
      override def interpretFirst[T](t: Expr[T] with First): T with First = interpret(t).first

      override def interpretSecond[T](t: Expr[T] with Second): T with Second = interpret(t).second
    }

    val tenList = ObjectFuncProvider.list[Nat._10]

    val res = {
      MGenerator.raw[Nat._4,
        ObjectFuncProvider[Interpreter] ::
          ObjectFuncProvider[IntConst] ::
          ObjectFuncProvider[BooleanConst] ::
          ObjectFuncProvider[StringConst] ::
          ObjectFuncProvider[Add] ::
          ObjectFuncProvider[Multiply] ::
          ObjectFuncProvider[Abs] ::
          ObjectFuncProvider[Concat] ::
          ObjectFuncProvider[And] ::
          ObjectFuncProvider[Or] :: HNil,
        gen.Repr,
        Interpreter => ((Int with Result) :+: (String with Result) :+: (Boolean with Result) :+: CNil),
        Options
      ](tenList, gen.to(t))(interpreter)
    }
    unsafeGet(res).asInstanceOf[T]
  }

  def main(args: Array[String]): Unit =
    println(
      interpret(
        Add(
          IntConst(2.result).first,
          IntConst(3.result).second
        )
      )
    )
}
