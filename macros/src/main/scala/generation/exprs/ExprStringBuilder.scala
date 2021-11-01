package generation.exprs

import shapeless.HList
import shapeless.HNil

import ExprBuilderGeneric._

import scala.util.Random

trait ContextStringBuilder {
  import ContextStringBuilder._
  def build(h: Any, a: Any): String

  def map(f: String => String): ContextStringBuilder = {
    from((h,a) => f(build(h, a)))
  }

  def flatMap(f: String => ContextStringBuilder): ContextStringBuilder =
    from((h,a) => f(build(h, a)).build(h, a))
}

object ContextStringBuilder {
  def from(f: (Any, Any) => String): ContextStringBuilder =
    (h: Any, a: Any) => f(h, a)

  implicit def const(s: String): ContextStringBuilder =
    from((_, _) => s)
}

class ExprStringBuilder[W[_]] extends ExprBuilderGeneric[ExprTree ,ContextStringBuilder, W] {

  protected implicit class StringMove(s: String) {
    def move(r: String = "  "): String = {
      s.split('\n').map(x => r + x).mkString("\n")
    }
  }

  import ContextStringBuilder._

  override def buildHNil: ContextStringBuilder = "HNil"

  override def buildHList(h: ExprTree, t: ExprTree): ContextStringBuilder = {
    for(
      hs <- build(h); ts <- build(t)
    ) yield s"$hs :: $ts"
  }

  override def buildCNil: ContextStringBuilder = "???"

  override def buildCoproduct(h1: ExprTree, t: ExprTree): ContextStringBuilder = {
    (h, a) => {
      val safeA = a.toString.split(Array('(', ')')).mkString("_")

      val r: String =
        if (t.typ == ExprType.CNilArg) {
          "case Inr(c: CNil) => c.impossible".move()
        } else {
          s"""|  case Inr(${safeA}_r) =>
              |${build(t).build(h, safeA + "_r").move("    ")}""".stripMargin

        }

      s"""|${a} match {
          |  case Inl(${safeA}_l) =>
          |${build(h1).build(h, safeA + "_l").move("    ")}
          |$r
          |}""".stripMargin
    }
  }

  override def buildSelectArg(n: Int): ContextStringBuilder = {
    (_, a) => {
      a match {
        case h: HList =>
          HList.unsafeGet(h, n).toString
        case s: String =>
          s"$s[$n]"
      }
    }
  }

  override def buildFromArg: ContextStringBuilder = (_, a) => a.toString

  override def buildSelectCtx(n: Int): ContextStringBuilder = {
    (h, _) => {
      h match {
        case h: HList =>
          HList.unsafeGet(h, n).toString
        case s: String =>
          s"$s[$n]"
      }
    }
  }

  override def buildApply(f: ExprTree, a: ExprTree): ContextStringBuilder =
    for(fs <- build(f); as <- build(a)) yield s"$fs($as)"

  override def buildApplyNative(name: String, f: W[(_) => _], memberFunc: Boolean, arg: ExprTree): ContextStringBuilder = {
    for(as <- build(arg)) yield {
      if(!memberFunc) {
        s"$name($as)"
      } else
        s"${as}.$name"
    }
  }

  override def buildPair(f: ExprTree, s: ExprTree): ContextStringBuilder = {
    for(fs <- build(f); ss <- build(s)) yield s"($fs, $ss)"
  }

  override def buildAbstractVal(b: ExprTree, isArgHList: Boolean, argType: W[String]): ContextStringBuilder = (h,a) => {
    a match {
      case a: HList =>
        val name = "a" + a.runtimeLength
        s"$name => ${build(b).build(h, name :: a)}"
      case a: String =>
        val name = "a" + Random.between(50, 150)
        s"$name => ${build(b).build(h, name :: a :: HNil)}"
    }

  }

  override def buildAbstractFun(b: ExprTree, argType: W[String]): ContextStringBuilder = (h,a) => {
    val name = "f" + h.asInstanceOf[HList].runtimeLength
    s"$name => ${build(b).build(name :: h.asInstanceOf[HList], a)}"
  }

  override def buildInlResult(a: ExprTree): ContextStringBuilder =
    for(as <- build(a)) yield s"Inl($as)"

  override def buildInrResult(a: ExprTree): ContextStringBuilder =
    for(as <- build(a)) yield s"Inr($as)"
}
