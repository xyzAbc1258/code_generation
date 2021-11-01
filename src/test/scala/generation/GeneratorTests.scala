package generation

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import shapeless._

import scala.{:: => _}

class GeneratorTests extends AnyFunSuite with Matchers {

  implicit class C[T](s :Seq[T]){
    def assertNonEmpty(): Seq[T] = {
      assert(s.nonEmpty)
      s
    }
  }
  
  test("From Args Single") {
    val s = "strdsdd"
    MGenerator[Nat._1, HNil, String, String]
      .expressions
      .assertNonEmpty()
      .foreach(x => assert(x.apply(HNil, s) == s))
  }

  test("From Args List") {
    val s = "strdsdd"
    MGenerator[Nat._1, HNil, String :: Int :: HList, String]
      .expressions
      .assertNonEmpty()
      .foreach(x => x.apply(HNil, s :: 12 :: HNil) shouldBe s)
  }

  test("From Ctx select") {
    case class Wrap(s: String)
    val s = "strdsdd"

    def f(string: String): Wrap = Wrap(string + "_exp")

    MGenerator[Nat._1, (String => Wrap) :: HNil, HNil, String => Wrap]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        (x.apply((f _) :: HNil, HNil)(s)) shouldBe f(s)
      }
  }

  test("From Ctx apply") {
    val s = 12568

    def f(int: Int): String = int + "_exp"

    MGenerator[Nat._1, (Int => String) :: HNil, Int, String]
      .expressions
      .assertNonEmpty()
      .foreach(x => assert(x.apply((f _) :: HNil, s) == f(s)))
  }

  test("Split coproduct") {
    val s = "strdsdd"
    val i = 12568

    def f(int: Int): String = int + "_exp"

    MGenerator[Nat._1, (Int => String) :: HNil, Int :+: String :+: CNil, String]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        x.apply((f _) :: HNil, Inl(i)) shouldBe f(i)
        x.apply((f _) :: HNil, Inr(Inl(s))) shouldBe s
      }
  }

  test("Apply multi argument function") {
    trait Semantic
    val s = "strdsdd"
    val i = 12568

    def f(int: Int)(s: String): (String with Semantic) = (int + s).asInstanceOf[String with Semantic]

    MGenerator[Nat._1, (Int => String => (String with Semantic)) :: HNil, Int :: String :: HNil, String with Semantic]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        x.apply((f _) :: HNil, i :: s :: HNil) shouldBe f(i)(s)
      }
  }

  test("Apply free poly function") {
    case class Wrap[S](s: S)
    case class Wrap2[S](s: S)
    val s = "strdsdd"

    def rewrap[S](s: Wrap[S]): Wrap2[S] = Wrap2(s.s)
    //There is a problem when type appears directly in signature without wrapping.
    //With wrapping type erasure takes care about "substituting" types
    MGenerator[Nat._1, (Wrap[Var1] => Wrap2[Var1]) :: HNil, Wrap[String], Wrap2[String]]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        x.apply((rewrap[Var1] _) :: HNil, Wrap(s)) shouldBe Wrap2(s)
      }
  }

  test("Apply object function") {
    case class Wrap(s: String)
    val s = "strdsdd"
    MGenerator[Nat._2, ObjectFuncProvider[Wrap] :: HNil, Wrap, String]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        x.apply(ObjectFuncProvider :: HNil, Wrap(s)) shouldBe s
      }
  }


  test("Apply generic object function") {
    case class Wrap[S](s: S)
    val s = "strdsdd"
    MGenerator[Nat._2, ObjectFuncProvider[Wrap[String]] :: HNil, Wrap[String], String]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        x.apply(ObjectFuncProvider :: HNil, Wrap(s)) shouldBe s
      }
  }


  test("Apply object polymorphic function") {
    case class Wrap[S](s: S)
    val s = "strdsdd"
    object Unwrapper {
      def unwrap[S](w: Wrap[S]): S = w.s
    }
    MGenerator[Nat._1, ObjectFuncProvider[Unwrapper.type] :: HNil, Unwrapper.type :: Wrap[String] :: HNil, String]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        x.apply(ObjectFuncProvider :: HNil, Unwrapper :: Wrap(s) :: HNil) shouldBe s
      }
  }

  test("Generate pair") {
    val s = "dasdsas"
    val i = 123686
    MGenerator[Nat._1, HNil, String :: Int :: HNil, (String, Int)]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        x.apply(HNil, s :: i :: HNil) shouldBe(s, i)
      }
  }

  test("Generate identity function") {
    val s = "sdsdasa"
    MGenerator[Nat._1, HNil, HNil, String => String]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        x.apply(HNil, HNil)(s) shouldBe s
      }
  }

  test("Generate more complex clean function (continuation monad bind operator)") {
    type Cont[T, S] = (S => T) => T

    def ret[S, T](s: S): Cont[T, S] = f => f(s)

    MGenerator[Nat._3, HNil, HNil, Cont[Int, String] => (String => Cont[Int, Double]) => Cont[Int, Double]]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        println(x.stringify[HNil, HNil](HNil, HNil))
        val >>= = x(HNil, HNil)
        val resultCont = >>=(ret("12"))(x => ret(x.toDouble + 1))
        resultCont(_.toInt) shouldBe 13
      }
  }

  test("Generate HList") {
    val s = "12"
    def parse(s: String): Int = s.toInt
    MGenerator[Nat._3, (String =>Int) :: HNil, String, String :: Int :: HNil]
      .expressions
      .assertNonEmpty()
      .foreach{x =>
        x(::((parse _),HNil) , s) shouldBe (s :: parse(s) :: HNil)
      }
  }

  test("Generate Coproduct") {
    val s = "12"
    MGenerator[Nat._3, HNil, String,  Int :+: String :+: CNil]
      .expressions
      .assertNonEmpty()
      .foreach{x =>
        x(HNil , s) shouldBe (Inr(Inl(s)))
      }
  }

  test("Proof of intuitionistic logic tautology") {
    trait P
    type ~[X] = X => Nothing
    MGenerator[Nat._2, HNil, HNil, ~[~[P :+: ~[P] :+: CNil]]]
      .expressions
      .assertNonEmpty()
      .foreach { x =>
        println(x.stringify(HNil, HNil)(null, null))
      }
  }

}
