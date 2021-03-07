package bshapeless.exprs

import bshapeless.{NamedStruct, SelectorWrapper}
import shapeless._
import shapeless.ops.hlist.Selector
import bshapeless.NamedStruct._

import scala.util.Random

sealed abstract class Expr[Ctx <: HList, A, +R](val typ: ExprType) extends ((Ctx, A) => R) with ExprTree {

  override type ATT = Expr[_, _, _]

  def size: Int

  protected implicit class StringMove(s: String) {
    def move(r: String = "  "): String = {
      s.split('\n').map(x => r + x).mkString("\n")
    }
  }

  def stringify[C1, A1](c: C1, a: A1)(implicit
    e1: NamedStruct.Aux[Ctx, String, C1],
    e2: NamedStruct.Aux[A, String, A1]
  ): String = ExprStringBuilder.build(this).build(c, a)

  def app[IM, R1](e: Expr[Ctx, A, IM])(implicit ev: R <:< (IM => R1)): Expr[Ctx, A, R1] =
    Apply(this.asInstanceOf[Expr[Ctx, A, IM => R1]], e)

}


object HNilCreate {

  case object HNilCreate extends Expr[Nothing, Any, HNil](ExprType.HNilTree) {

    override def apply(ctx: Nothing, a: Any): HNil = HNil

    override def size: Int = 1

    def build[R](b: ExprBuilder[ATT, R]): R = b.buildHNil
  }

  def apply[Ctx <: HList, A]: Expr[Ctx, A, HNil] =
    HNilCreate.asInstanceOf[Expr[Ctx, A, HNil]]
}

case class HListResultSplit[Ctx <: HList, A, R1, RR <: HList](
  headExpr: Expr[Ctx, A, R1],
  tailExpr: Expr[Ctx, A, RR]
) extends Expr[Ctx, A, R1 :: RR](ExprType.HListResult) {
  override def apply(ctx: Ctx, a: A): R1 :: RR =
    headExpr(ctx, a) :: tailExpr(ctx, a)

  override def size: Int = headExpr.size + tailExpr.size + 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildHList(headExpr, tailExpr)
}

object CNilCreate {

  case object CNilCreate extends Expr[Nothing, CNil, Nothing](ExprType.CNilArg) {
    override def apply(v1: Nothing, v2: CNil): Nothing = v2.impossible

    override def size: Int = 1

    def build[R](b: ExprBuilder[ATT, R]): R = b.buildCNil
  }

  def apply[Ctx <: HList, R]: Expr[Ctx, CNil, R] =
    CNilCreate.asInstanceOf[Expr[Ctx, CNil, R]]
}

case class CoproductArgSplit[Ctx <: HList, A, AR <: Coproduct, R](
  inlExpr: Expr[Ctx, A, R],
  inrExpr: Expr[Ctx, AR, R]
) extends Expr[Ctx, A :+: AR, R](ExprType.CoproductArgs) {

  override def apply(v1: Ctx, v2: A :+: AR): R =
    v2.eliminate(inlExpr(v1, _), inrExpr(v1, _))

  override def size: Int = inlExpr.size + inrExpr.size + 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildCoproduct(inlExpr, inrExpr)
}

case class FromArgsSelect[Ctx <: HList, A <: HList, R](
  s: SelectorWrapper[A, R]
) extends Expr[Ctx, A, R](ExprType.SelectArgs) {

  override def apply(v1: Ctx, v2: A): R = s(v2)

  override def size: Int = 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildSelectArg(s.index)
}

object FromArgsSelect {
  def apply[Ctx <: HList, A <: HList, R](n: Int): FromArgsSelect[Ctx, A, R] =
    new FromArgsSelect(SelectorWrapper(n))
}

case class FromArgsEq[Ctx <: HList, A, R](
  ev: A <:< R
) extends Expr[Ctx, A, R](ExprType.FromArgsEq) {

  override def apply(v1: Ctx, v2: A): R = ev(v2)

  override def size: Int = 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildFromArg
}

object FromArgsEq {
  def create[C <: HList, R <: A, A]: FromArgsEq[C, R, A] = new FromArgsEq[C,R, A](implicitly)
}

case class FromCtxSelect[Ctx <: HList, A, R](
  s: SelectorWrapper[Ctx, _ <: R]
) extends Expr[Ctx, A, R](ExprType.SelectCtx) {
  override def apply(v1: Ctx, v2: A): R = s(v1)

  override def size: Int = 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildSelectCtx(s.index)
}

object FromCtxSelect {
  def apply[Ctx <: HList, A, R](n: Int): FromCtxSelect[Ctx, A, R] =
    new FromCtxSelect[Ctx, A, R](SelectorWrapper(n))
}

case class Apply[Ctx <: HList, A, Arg, Res](
  e: Expr[Ctx, A, Arg => Res],
  a: Expr[Ctx, A, Arg]
) extends Expr[Ctx, A, Res](ExprType.Apply) {

  override def apply(v1: Ctx, v2: A): Res = {
    e(v1, v2)(a(v1, v2))
  }

  override def size: Int = e.size + a.size + 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildApply(e, a)
}

case class ApplyNative[Ctx <: HList, A, Arg, Res](
  e: Expr[Ctx, A, Arg])(
  f: Arg => Res,
  name: String,
  memberFunc: Boolean = false
) extends Expr[Ctx, A, Res](ExprType.ApplyNative) {
  override def apply(v1: Ctx, v2: A): Res = f(e(v1, v2))

  override def size: Int = e.size + 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildApplyNative(name, memberFunc, e)
}

case class PairExp[Ctx <: HList, A, L1, L2](
  e1: Expr[Ctx, A, L1],
  e2: Expr[Ctx, A, L2]
) extends Expr[Ctx, A, (L1, L2)](ExprType.Pair) {
  override def size: Int = e1.size + e2.size + 1

  override def apply(v1: Ctx, v2: A): (L1, L2) =
    (e1(v1, v2), e2(v1, v2))

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildPair(e1, e2)
}

case class AbstractVal[Ctx <: HList, A <: HList, Arg, Res](
  e: Expr[Ctx, Arg :: A, Res]
) extends Expr[Ctx, A, Arg => Res](ExprType.AbstractVal) {

  override def apply(v1: Ctx, v2: A): Arg => Res =
    a => e(v1, a :: v2)

  override def size: Int = e.size + 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildAbstractVal(e)
}

case class AbstractValNotH[Ctx <: HList, A, Arg, Res](
  e: Expr[Ctx, Arg :: A :: HNil, Res]
) extends Expr[Ctx, A, Arg => Res](ExprType.AbstractVal) {

  override def apply(v1: Ctx, v2: A): Arg => Res =
    a => e(v1, a :: v2 :: HNil)

  override def size: Int = e.size + 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildAbstractVal(e)
}


case class AbstractFunc[Ctx <: HList, A, Arg, Res](
  e: Expr[Arg :: Ctx, A, Res]
) extends Expr[Ctx, A, Arg => Res](ExprType.AbstractFun) {

  override def apply(v1: Ctx, v2: A): Arg => Res =
    a => e(a :: v1, v2)

  override def size: Int = e.size + 1

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildAbstractFun(e)
}

case class WithMapCtx[Ctx <: HList, NCtx <: HList, Args,R](
  f: Ctx => NCtx, // selecting subset of HList, so its applicable in stringify
  e: Expr[NCtx, Args, R]
) extends Expr[Ctx, Args, R](null) {

  override def size: Int = e.size

  override def apply(c: Ctx, a: Args): R = e(f(c), a)

  override def hashCode(): Int = e.hashCode()

  override def equals(o: Any): Boolean = o match {
    case x: WithMapCtx[Ctx, NCtx, Args, R] => equals(x.e)
    case x: Expr[NCtx, Args, R] => x.equals(this.e)
    case _ => false
  }

  def build[R](b: ExprBuilder[ATT, R]): R = ???
}

case class InlResultExpr[C <: HList, A, L, R <: Coproduct](
  e: Expr[C, A, L]
) extends Expr[C, A, L :+: R](ExprType.InlResult) {
  override def size: Int = e.size + 1

  override def apply(v1: C, v2: A): L :+: R = Inl(e(v1, v2))

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildInlResult(e)
}

case class InrResultExpr[C <: HList, A, L, R <: Coproduct](
  e: Expr[C, A, R]
) extends Expr[C, A, L :+: R](ExprType.InrResult) {
  override def size: Int = e.size + 1

  override def apply(v1: C, v2: A): L :+: R = Inr(e(v1, v2))

  def build[R](b: ExprBuilder[ATT, R]): R = b.buildInrResult(e)
}