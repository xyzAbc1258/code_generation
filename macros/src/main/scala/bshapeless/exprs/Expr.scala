package bshapeless.exprs

import bshapeless.{NamedStruct, SelectorWrapper}
import shapeless._
import shapeless.ops.hlist.Selector
import bshapeless.NamedStruct._

import scala.util.Random

sealed trait Expr[Ctx <: HList, A, +R] extends ((Ctx, A) => R) {

  def size: Int

  protected implicit class StringMove(s: String) {
    def move(r: String = "  "): String = {
      s.split('\n').map(x => r + x).mkString("\n")
    }
  }

  def stringify[C1, A1](c: C1, a: A1)(implicit
    e1: NamedStruct.Aux[Ctx, String, C1],
    e2: NamedStruct.Aux[A, String, A1]
  ): String = innerStringify(c, a)

  protected def innerStringify[C1, A1](h: C1, a: A1)(implicit
    e1: NamedStruct.Aux[Ctx, String, C1],
    e2: NamedStruct.Aux[A, String, A1]
  ): String

  def app[IM, R1](e: Expr[Ctx, A, IM])(implicit ev: R <:< (IM => R1)): Expr[Ctx, A, R1] =
    Apply(this.asInstanceOf[Expr[Ctx, A, IM => R1]], e)

}


object HNilCreate {

  case object HNilCreate extends Expr[Nothing, Any, HNil] {

    override def apply(ctx: Nothing, a: Any): HNil = HNil

    override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Nothing, String, C1], e2: Aux[Any, String, A1]): String = {
      "HNil"
    }

    override def size: Int = 1
  }

  def apply[Ctx <: HList, A]: Expr[Ctx, A, HNil] =
    HNilCreate.asInstanceOf[Expr[Ctx, A, HNil]]
}

case class HListResultSplit[Ctx <: HList, A, R1, RR <: HList](
  headExpr: Expr[Ctx, A, R1],
  tailExpr: Expr[Ctx, A, RR]
) extends Expr[Ctx, A, R1 :: RR] {
  override def apply(ctx: Ctx, a: A): R1 :: RR =
    headExpr(ctx, a) :: tailExpr(ctx, a)

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A, String, A1]): String = {
    s"${headExpr.stringify(h, a)}::${tailExpr.stringify(h, a)}"
  }

  override def size: Int = headExpr.size + tailExpr.size + 1
}

object CNilCreate {

  case object CNilCreate extends Expr[Nothing, CNil, Nothing] {
    override def apply(v1: Nothing, v2: CNil): Nothing = v2.impossible

    override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Nothing, String, C1], e2: Aux[CNil, String, A1]): String =
      "???"

    override def size: Int = 1
  }

  def apply[Ctx <: HList, R]: Expr[Ctx, CNil, R] =
    CNilCreate.asInstanceOf[Expr[Ctx, CNil, R]]
}

case class CoproductArgSplit[Ctx <: HList, A, AR <: Coproduct, R](
  inlExpr: Expr[Ctx, A, R],
  inrExpr: Expr[Ctx, AR, R]
) extends Expr[Ctx, A :+: AR, R] {

  override def apply(v1: Ctx, v2: A :+: AR): R =
    v2.eliminate(inlExpr(v1, _), inrExpr(v1, _))

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A :+: AR, String, A1]): String = {
    val safeA = a.toString.split(Array('(', ')')).mkString("_")

    val r =
      if (inrExpr.equals(CNilCreate.apply[Ctx, R]))
        s"case Inr(c: CNil) => c.impossible".move()
      else
        s"""|  case Inr(${safeA}_r) =>
            |${inrExpr.stringify(h, safeA + "_r")(e1, null).move("    ")}""".stripMargin



    s"""|${a} match {
        |  case Inl(${safeA}_l) =>
        |${inlExpr.stringify(h, safeA + "_l")(e1, null).move("    ")}
        |$r
        |}""".stripMargin
  }

  override def size: Int = inlExpr.size + inrExpr.size + 1
}

case class FromArgsSelect[Ctx <: HList, A <: HList, R](
  s: SelectorWrapper[A, R]
) extends Expr[Ctx, A, R] {

  override def apply(v1: Ctx, v2: A): R = s(v2)

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A, String, A1]): String = {
    a match {
      case h: HList =>
        s.selector[HList, String](h)
      case str: String =>
        s"$str[${s.index}]"
    }

  }

  override def size: Int = 1
}

object FromArgsSelect {
  def apply[Ctx <: HList, A <: HList, R](n: Int): FromArgsSelect[Ctx, A, R] =
    new FromArgsSelect(SelectorWrapper(n))
}

case class FromArgsEq[Ctx <: HList, A, R](
  ev: A <:< R
) extends Expr[Ctx, A, R] {

  override def apply(v1: Ctx, v2: A): R = ev(v2)

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A, String, A1]): String =
    a.toString

  override def size: Int = 1
}

object FromArgsEq {
  def create[C <: HList, R <: A, A]: FromArgsEq[C, R, A] = new FromArgsEq[C,R, A](implicitly)
}

case class FromCtxSelect[Ctx <: HList, A, R](
  s: SelectorWrapper[Ctx, _ <: R]
) extends Expr[Ctx, A, R] {
  override def apply(v1: Ctx, v2: A): R = s(v1)

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A, String, A1]): String = {
    h match {
      case h: HList =>
        s.selector[HList, String](h)
      case str: String =>
        s"$str[${s.index}]"
    }
  }

  override def size: Int = 1
}

object FromCtxSelect {
  def apply[Ctx <: HList, A, R](n: Int): FromCtxSelect[Ctx, A, R] =
    new FromCtxSelect[Ctx, A, R](SelectorWrapper(n))
}

case class Apply[Ctx <: HList, A, Arg, Res](
  e: Expr[Ctx, A, Arg => Res],
  a: Expr[Ctx, A, Arg]
) extends Expr[Ctx, A, Res] {

  override def apply(v1: Ctx, v2: A): Res = {
    e(v1, v2)(a(v1, v2))
  }

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A, String, A1]): String = {
    s"${e.stringify(h, a)}(${this.a.stringify(h, a)})"
  }

  override def size: Int = e.size + a.size + 1
}

case class ApplyNative[Ctx <: HList, A, Arg, Res](
  e: Expr[Ctx, A, Arg])(
  f: Arg => Res,
  name: String,
  memberFunc: Boolean = false
) extends Expr[Ctx, A, Res] {
  override def apply(v1: Ctx, v2: A): Res = f(e(v1, v2))

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A, String, A1]): String = {
    if(!memberFunc)
      s"$name(${e.stringify(h, a)})"
    else
      s"${e.stringify(h, a)}.$name"
  }

  override def size: Int = e.size + 1
}

case class PairExp[Ctx <: HList, A, L1, L2](
  e1: Expr[Ctx, A, L1],
  e2: Expr[Ctx, A, L2]
) extends Expr[Ctx, A, (L1, L2)] {
  override def size: Int = e1.size + e2.size + 1

  override def apply(v1: Ctx, v2: A): (L1, L2) =
    (e1(v1, v2), e2(v1, v2))

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit ee1: Aux[Ctx, String, C1], ee2: Aux[A, String, A1]): String = {
    s"(${e1.stringify(h, a)}, ${e2.stringify(h, a)})"
  }
}
case class AbstractVal[Ctx <: HList, A <: HList, Arg, Res](
  e: Expr[Ctx, Arg :: A, Res]
) extends Expr[Ctx, A, Arg => Res] {

  override def apply(v1: Ctx, v2: A): Arg => Res =
    a => e(v1, a :: v2)

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A, String, A1]): String = {
    val name = "a" + a.asInstanceOf[HList].runtimeLength
    s"$name => ${e.stringify(h, name :: (a.asInstanceOf[HList]))(e1, null)}"
  }

  override def size: Int = e.size + 1
}

case class AbstractValNotH[Ctx <: HList, A, Arg, Res](
  e: Expr[Ctx, Arg :: A :: HNil, Res]
) extends Expr[Ctx, A, Arg => Res] {

  override def apply(v1: Ctx, v2: A): Arg => Res =
    a => e(v1, a :: v2 :: HNil)

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A, String, A1]): String = {
    val name = "a" + Random.between(50, 150)
    s"$name => ${e.stringify(h, name :: a :: HNil)(e1, null)}"
  }

  override def size: Int = e.size + 1
}


case class AbstractFunc[Ctx <: HList, A, Arg, Res](
  e: Expr[Arg :: Ctx, A, Res]
) extends Expr[Ctx, A, Arg => Res] {

  override def apply(v1: Ctx, v2: A): Arg => Res =
    a => e(a :: v1, v2)

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[Ctx, String, C1], e2: Aux[A, String, A1]): String = {
    val name = "f" + a.asInstanceOf[HList].runtimeLength
    s"$name => ${e.stringify(name :: h.asInstanceOf[HList], a)(null, e2)}"
  }

  override def size: Int = e.size + 1
}

case class WithMapCtx[Ctx <: HList, NCtx <: HList, Args,R](
  f: Ctx => NCtx, // selecting subset of HList, so its applicable in stringify
  e: Expr[NCtx, Args, R]
) extends Expr[Ctx, Args, R] {

  override def size: Int = e.size

  override def apply(c: Ctx, a: Args): R = e(f(c), a)

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: NamedStruct.Aux[Ctx, String, C1], e2: NamedStruct.Aux[Args, String, A1]): String = {
    e.stringify(f.asInstanceOf[C1 => NCtx](h), a)(NamedStruct.instance, e2)
  }

  override def hashCode(): Int = e.hashCode()

  override def equals(o: Any): Boolean = o match {
    case x: WithMapCtx[Ctx, NCtx, Args, R] => equals(x.e)
    case x: Expr[NCtx, Args, R] => x.equals(this.e)
    case _ => false
  }
}

case class InlResultExpr[C <: HList, A, L, R <: Coproduct](
  e: Expr[C, A, L]
) extends Expr[C, A, L :+: R] {
  override def size: Int = e.size + 1

  override def apply(v1: C, v2: A): L :+: R = Inl(e(v1, v2))

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[C, String, C1], e2: Aux[A, String, A1]): String = {
    s"Inl(${e.stringify(h, a)})"
  }
}

case class InrResultExpr[C <: HList, A, L, R <: Coproduct](
  e: Expr[C, A, R]
) extends Expr[C, A, L :+: R] {
  override def size: Int = e.size + 1

  override def apply(v1: C, v2: A): L :+: R = Inr(e(v1, v2))

  override protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[C, String, C1], e2: Aux[A, String, A1]): String = {
    s"Inr(${e.stringify(h, a)})"
  }
}

case class ExchangeArgs[C <: HList, A, A2, R](
  selectorWrapper: SelectorWrapper[C, A => A2],
  inner: Expr[C, A2, R]
) extends Expr[C, A, R] {
  override def size: Int = inner.size + 1

  protected def innerStringify[C1, A1](h: C1, a: A1)(implicit e1: Aux[C, String, C1], e2: Aux[A, String, A1]): String = {
    val funName = selectorWrapper.selector[HList, String].apply(h.asInstanceOf[HList])
    assert(a.isInstanceOf[String])
    inner.stringify(h, s"$funName($a)")
  }

  override def apply(v1: C, v2: A): R = {
    inner(v1, selectorWrapper(v1)(v2))
  }

}