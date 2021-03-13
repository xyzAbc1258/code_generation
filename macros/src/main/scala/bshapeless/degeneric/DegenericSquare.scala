package bshapeless.degeneric

import bshapeless.CommonUtils
import shapeless._

import scala.collection.immutable
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

trait Fold {
  type Constraint

  type Zero <: Constraint
  type First[A] <: Constraint
  type Fold[H, R <: Constraint] <: Constraint
}

object Fold {
  type Intersection = Intersection.type
  type HList = HList.type

  object Intersection extends Fold {
    override type Constraint = Any

    override type Zero = Any
    override type First[A] = A
    override type Fold[H, R] = H with R
  }

  object HList extends Fold {
    override type Constraint = shapeless.HList

    override type Zero = HNil
    override type First[A] = A :: HNil
    override type Fold[H, R <: shapeless.HList] = H :: R
  }

}


trait DegenericSquare[H1 <: HList, H2 <: HList, F[_,_], Folder <: Fold] {
  type Out <: Folder#Constraint
}

object DegenericSquare {
  def apply[H1 <: HList, H2 <: HList, F[_, _], Folder <: Fold](implicit e: DegenericSquare[H1,H2,F, Folder]): e.type = e

  implicit def mkInstance[H1 <: HList, H2 <: HList, F[_,_], Folder <: Fold]: DegenericSquare[H1,H2,F, Folder] = macro Macro.make[H1,H2,F, Folder]

  class Macro(val c: whitebox.Context) extends CommonUtils {

    override type U = c.universe.type
    override val u: c.universe.type = c.universe

    import u._

    //import c.universe._

    def make[H1 <: HList : c.WeakTypeTag, H2 <: HList : c.WeakTypeTag, F[_,_], Folder <: Fold: c.WeakTypeTag](implicit ft: c.WeakTypeTag[F[_,_]]): c.Tree = {
      val h1Types = Types.split2ArgsRec(weakTypeOf[H1], Types.hconsType)
      val h2Types = Types.split2ArgsRec(weakTypeOf[H2], Types.hconsType)
      val connector = weakTypeOf[F[_,_]].typeConstructor
      val finalTypes = for(t1 <- h1Types; t2 <- h2Types) yield appliedType(connector, t1, t2)
      def collectType(name: String): Type = weakTypeOf[Folder].dealias.members
        .collectFirst{case x if x.isType && x.name.decodedName.toString == name => x.asType.info}
        .getOrElse(sys.error(s"Couldnt get type $name"))
        .dealias
      val zeroT = collectType("Zero")
      val single = collectType("First").typeConstructor
      val fold = collectType("Fold").typeConstructor
      val outType = finalTypes match {
        case immutable.::(_, _) =>
          val end = appliedType(single, finalTypes.last)
          finalTypes.init.foldRight(end){case (t, r) => appliedType(fold, t, r)}
        case Nil => zeroT
      }
      q"""new DegenericSquare[
          ${TypeTree(weakTypeOf[H1])},
          ${TypeTree(weakTypeOf[H2])},
          ${TypeTree(weakTypeOf[F[_,_]])},
          ${TypeTree(weakTypeOf[Folder])}]{
         type Out = ${TypeTree(outType)}
       }"""
    }

  }
}
