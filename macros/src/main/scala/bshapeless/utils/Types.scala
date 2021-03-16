package bshapeless.utils

import bshapeless.ObjectFuncProvider
import bshapeless.Var

import scala.annotation.tailrec
import scala.reflect.api.Universe

class Types[U <: Universe with Singleton](val u: U) {
  import u._

  val objectProviderTpe: Type = weakTypeOf[ObjectFuncProvider[_]]

  val hlistType: Type = weakTypeOf[shapeless.HList]
  val hnilType: Type = weakTypeOf[shapeless.HNil]
  val hconsType: Type = weakTypeOf[shapeless.::[_, _]]

  val coproductType: Type = weakTypeOf[shapeless.Coproduct]
  val cnilType: Type = weakTypeOf[shapeless.CNil]
  val cconsType: Type = weakTypeOf[shapeless.:+:[_, _]]

  val natType: Type = weakTypeOf[shapeless.Nat]
  val zeroType: Type = weakTypeOf[shapeless._0]
  val succType: Type = weakTypeOf[shapeless.Succ[_]]

  val funcType: Type = weakTypeOf[(_) => _]
  val pairType: Type = weakTypeOf[(_, _)]

  val varType: Type = weakTypeOf[Var]

  def split2ArgsRec(t: Type, connectType: Type): Seq[Type] = {
    var tt = t.dealias
    var s = Seq[Type]()
    while (tt <:< connectType) {
      s = tt.typeArgs.head +: s
      tt = tt.typeArgs(1).dealias
    }
    s.reverse
  }

  def size(t: Type): Int = {
    sizer(t.dealias)
  }

  def hash(t: Type): Int = {
    @tailrec
    def inner(it: Seq[Type], c: Int): Int =
      it match {
        case h +: t =>
          inner(h.typeArgs.map(_.dealias) ++: t, c * 41 +
            h.typeConstructor.dealias.typeSymbol.name.decodedName.toString.hashCode)
        case Seq() => c
      }
    inner(Seq(t.dealias), 0)
  }

  @tailrec
  private final def sizer(t: Type, r: Seq[Type] = Seq(), im: Int = 0): Int = {
    if (t.typeArgs.nonEmpty) {
      sizer(t.typeArgs.head.dealias, t.typeArgs.tail.map(_.dealias) ++: r, im + 1)
    } else {
      if (r.isEmpty) im + 1
      else sizer(r.head, r.tail, im + 1)
    }
  }
}