package generation.`implicit`

import generation.MGenerator
import shapeless.:+:
import shapeless.::
import shapeless.CNil
import shapeless.Generic
import shapeless.HNil
import shapeless.Nat

object Expr {

  def xx2(): Unit = {
    trait Tag
    trait Partial extends Tag
    trait Part extends Tag
    trait Sum extends Tag
    implicit class Tagged[T](v: T) {
      def tag[V <: Tag]: T with V = v.asInstanceOf[T with V]
    }

    sealed trait IntList
    case object IntNil extends IntList
    case class IntCons(i: Int, c: IntList) extends IntList


    val gen = Generic[IntList] //gen.Repr = IntNil.type :+: IntCons :+: CNil
    //Generic[IntCons].Repr = Int :: IntList :: HNil
    val eg = MGenerator[
      Nat._5,
      ((Int with Part) => (Int with Partial) => (Int with Sum)) ::
        ((IntList with Part) => (Int with Partial)) ::
        (IntCons => (IntList with Part)) ::
        (IntCons => (Int with Part)) ::
        ((Int with Part) => (Int with Part)) ::
        (IntNil.type => Int with Sum) ::
        HNil,
      gen.Repr, //IntNil.type :+: IntCons :+: CNil
      (Int with Sum)
    ]

    for (e <- eg.expressions) {
      println(e.stringify(
        "concat" :: "recurse" :: "tail" :: "head" :: "map" :: "zero" :: HNil,
        "list"))
    }

    def op(
      concat: (Int, Int) => Int,
      zero: Int,
      value: Int => Int = x => x
    ): IntList => Int = {
      def make(eval: => IntList => Int)(i: IntList): Int = {
        eg.expressions.head.apply(
          ((x: Int with Part) => (y: Int with Partial) => concat(x, y).tag[Sum]) ::
            ((x: IntList with Part) => eval(x).tag[Partial]) ::
            ((x: IntCons) => x.c.tag[Part]) ::
            ((x: IntCons) => value(x.i).tag[Part]) ::
            ((x: Int with Part) => x) ::
            ((_: IntNil.type) => zero.tag[Sum]) ::
            HNil,
          gen.to(i)
        )
      }

      def fixpoint: IntList => Int = make(fixpoint)

      fixpoint
    }

    def sum: IntList => Int = op(_ + _, 0)

    def mul: IntList => Int = op(_ * _, 1)

    def length: IntList => Int = op(_ + _, 0, _ => 1)

    val list = IntCons(1, IntCons(2, IntCons(3, IntCons(4, IntNil))))
    println("Sum should be 10, is: " + sum(list))
    println("Mul should be 24, is: " + mul(list))
    println("Length should be 4, is: " + length(list))

  }

  def xx8(): Unit = {
    val g = MGenerator[
      Nat._3,
      (String => String) :: HNil,
      String :+: CNil,
      (String :: HNil) :: HNil
    ]
    for (e <- g.expressions) {
      val s = e.stringify("f" :: HNil, "s")
      println(s)
    }

  }

  def main(args: Array[String]): Unit = {
    buildFilter[Int, Nothing](x => x, 0)
    //xx4()
    //xx2()
    //xx8()
  }

  def xx3(): Unit = {
    val g = MGenerator[
      Nat._1,
      (Int => String) :: (String => Int) :: (Int => Int) :: HNil,
      Int,
      Int
    ]
    for (e <- g.expressions.toList.sortBy(_.size)) {
      println(e.stringify(
        "show" :: "parse" :: "inc" :: HNil,
        "x"
      ))
    }
  }


  def xx4[T, R](): Unit = {
    trait Tail
    val gen = new Generic[List[T]] {
      override type Repr = Nil.type :+: scala.::[T] :+: CNil

      override def to(t: List[T]): Repr = ???

      override def from(r: Repr): List[T] = ???
    }
    val eg = MGenerator[
      Nat._3,
      (R => T => R) :: //combine
        ((List[T]) => R) :: //recurse
        (scala.::[T] => (List[T])) :: // tail
        (scala.::[T] => T) :: //head
        (Nil.type => R) :: //zero
        HNil,
      gen.Repr,
      R
    ]

    for (e <- eg.expressions.toList.sortBy(_.size)) {
      println(e.stringify(
        "concat" :: "recurse" :: "tail" :: "head" :: "zero" :: HNil,
        "list"))
      println("----------------------------")
    }
  }

  def xx5(): Unit = {}

  def buildFilter[T, R](f: R => T, v: T): List[R] => Option[R] = {
    trait A
    val g = MGenerator[
      Nat._7,
      (List[R] => (R => Boolean) => Option[R]) ::
        (R => T) ::
        (T => (T with A) => Boolean) ::
        HNil,
      (T with A) :: HNil,
      List[R] => Option[R]
    ]
    for (e <- g.expressions) {
      println(e.stringify("filter" :: "select" :: "eq" :: HNil, "comparand" :: HNil))
    }
    g.expressions.head.apply(
      ((x: List[R]) => (f: R => Boolean) => x.find(f)) ::
        f ::
        ((x: T) => (y: T with A) => x == y) ::
        HNil,
      (v.asInstanceOf[T with A]) :: HNil)
  }
}
