package bshapeless.degeneric

import bshapeless.CommonUtils
import shapeless.HList

import scala.collection.immutable
import scala.reflect.macros.whitebox
import scala.language.experimental.macros

trait Degeneric2[H1 <: HList, H2 <: HList, F[_, _], Folder <: Fold] {
  type Out <: Folder#Constraint
}

object Degeneric2 {
  def apply[H1 <: HList, H2 <: HList, F[_, _], Folder <: Fold](implicit e: Degeneric2[H1, H2, F, Folder]): e.type = e

  implicit def mkInstance[H1 <: HList, H2 <: HList, F[_, _], Folder <: Fold]: Degeneric2[H1, H2, F, Folder] = macro Macro.make[H1, H2, F, Folder]

  class Macro(val c: whitebox.Context) extends CommonUtils {

    import c.universe._

    def make[H1 <: HList : c.WeakTypeTag, H2 <: HList : c.WeakTypeTag, F[_, _], Folder <: Fold : c.WeakTypeTag](implicit ft: c.WeakTypeTag[F[_, _]]): c.Tree = {
      val h1Types = Types.split2ArgsRec(weakTypeOf[H1], Types.hconsType)
      val h2Types = Types.split2ArgsRec(weakTypeOf[H2], Types.hconsType)
      if (h1Types.size != h2Types.size)
        sys.error(s"List of types must have same size. Got: ${h1Types.size} and ${h2Types.size}")
      val connector = weakTypeOf[F[_, _]].typeConstructor
      val finalTypes = for ((t1, t2) <- h1Types.zip(h2Types)) yield appliedType(connector, t1, t2)

      def collectTypeT(t: Type, name: String): Type = t.members
        .collectFirst { case x if x.isType && x.name.decodedName.toString == name => x.asType.info }
        .getOrElse(sys.error(s"Couldnt get type $name"))

      def collectType(name: String): Type = collectTypeT(weakTypeOf[Folder].dealias, name)

      val zeroT = collectType("Zero").dealias
      val single = collectType("First").dealias.typeConstructor
      val fold = collectType("Fold").dealias.typeConstructor

      def foldTypes(typeLists: List[List[Type]], lastType: Type, trees: List[Tree]): (Type, List[Tree]) = {
        typeLists match {
          case ::(_, _) =>
            val lastList = typeLists.last
            val nt = lastList.foldRight(lastType) { case (t, r) => appliedType(fold, t, r) }

            val literalName = "Out" + trees.size
            val name = TypeName(literalName)
            val objLiteralName = "OutObj" + trees.size
            val objName = TermName(objLiteralName)
            val newTree = q"object $objName { type $name = ${TypeTree(nt)} }"
            val typed = c.typecheck(newTree)
            val typedType = typed.symbol.asModule.info
            val t = c.internal.typeRef(typedType, typedType.member(name), Nil)

            c.info(c.enclosingPosition, "Generated type: " + t, true)

            foldTypes(typeLists.init, t, typed :: trees)
          case Nil => (lastType, trees)
        }
      }

      val (outType, trees) = finalTypes match {
        case immutable.::(_, _) =>
          val end = appliedType(single, finalTypes.last)
          foldTypes(finalTypes.init.grouped(20).toList, end, Nil)
        case Nil => (zeroT, Nil)
      }
      q"""
          new Degeneric2[
          ${TypeTree(weakTypeOf[H1])},
          ${TypeTree(weakTypeOf[H2])},
          ${TypeTree(weakTypeOf[F[_, _]])},
          ${TypeTree(weakTypeOf[Folder])}]{
          ..$trees
         type Out = ${TypeTree(outType)}
       }"""
    }

  }

}
