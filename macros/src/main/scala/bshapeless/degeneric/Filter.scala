package bshapeless.degeneric

import bshapeless.CommonUtils
import shapeless.HList

import scala.annotation.tailrec
import scala.reflect.macros.whitebox
import scala.language.experimental.macros

trait Filter[H <: HList, TFs <: HList, T] {
  type Out <: HList
}

object Filter {
  def apply[H1 <: HList, TFs <: HList, T](implicit e: Filter[H1,TFs, T]): e.type = e

  implicit def mkInstance[H1 <: HList, TFs <: HList, T]: Filter[H1,TFs, T] = macro Macro.make[H1,TFs, T]

  class Macro(val c: whitebox.Context) extends CommonUtils {
    import c.universe._

    def make[H1 <: HList : c.WeakTypeTag, TFs <: HList : c.WeakTypeTag, T: c.WeakTypeTag]: c.Tree = {
      val h1Types = Types.split2ArgsRec(weakTypeOf[H1], Types.hconsType)
      val h2Types = Types.split2ArgsRec(weakTypeOf[TFs], Types.hconsType)
      if(h1Types.size != h2Types.size)
        sys.error(s"Same size ${h1Types.size} ${h2Types.size}")
      val t = weakTypeOf[T]
      val filtered = h1Types.zip(h2Types).filter(_._2 <:< t).map(_._1)
      @tailrec
      def partFold(toFold:List[List[Type]], end: Type, trees: List[Tree]):(Type, List[Tree]) = {
        toFold match {
          case ::(head, next) =>
            val nType = head.foldRight(end)(_ :::: _)
            val nTree = TypeDef(NoMods, TypeName("Out_" + trees.size), Nil, TypeTree(nType))
            val typed = c.typecheck(nTree, c.TERMmode)
            partFold(next, typed.symbol.asType.toType, typed :: trees)
          case Nil => (end, trees.reverse)
        }
      }
      val (outType, irs) = partFold(filtered.grouped(10).toList, Types.hnilType, Nil)
      q"""{
            type T1 = ${TypeTree(weakTypeOf[H1])}
            type T2 = ${TypeTree(weakTypeOf[TFs])}
            new Filter[T1,T2,${TypeTree(weakTypeOf[T])}]{
              ..$irs
              type Out = ${TypeTree(outType)}
            }
          }"""
    }
  }
}