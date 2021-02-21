package shapeless.exprs

import shapeless._

import scala.language.experimental.macros
import scala.reflect.macros.whitebox

case class Cached2[+T](value: T) extends AnyVal

object Cached2 {
  implicit def materialize[I]: Cached2[I] = macro CachedMacros2.materializeCached[I]

  def implicitly[T](implicit cached: Cached2[T]): T = cached.value
}

object CachedMacros2

class CachedPerMainImplicit {
  var cache = Map.empty[Any, List[(Any, Any)]]
  var hitp = 0
  var hitn = 0
  var misses = 0
}

class CachedMacrosState2 {
  var map = List.empty[(Any, CachedPerMainImplicit)]
}

class CachedMacros2(override val c: whitebox.Context) extends LazyMacros(c) with OpenImplicitMacros {

  import c.universe._

  private val bigState = MacroState.getOrElseUpdate[CachedMacrosState2](c.universe, new CachedMacrosState2)

  private val state: CachedPerMainImplicit = {
    val r = bigState.map.find(_._1.asInstanceOf[Type] =:= mostGeneralImplicit)
    r match {
      case Some((_, value)) =>
        value
      case None =>
        val v = new CachedPerMainImplicit
        bigState.map = (mostGeneralImplicit, v) :: bigState.map
        v
    }
  }

  def mostGeneralImplicit: Type =
    c.openImplicits.last.pt.dealias

  def deepCopyTree(t: Tree): Tree = {
    val treeDuplicator = new Transformer {
      // by default Transformers don’t copy trees which haven’t been modified,
      // so we need to use use strictTreeCopier
      override val treeCopy =
      c.asInstanceOf[reflect.macros.runtime.Context].global.newStrictTreeCopier.asInstanceOf[TreeCopier]
    }

    treeDuplicator.transform(t)
  }

  def materializeCached[T: WeakTypeTag]: Tree = {
    val forced = false
    // Getting the actual type parameter T, using the same trick as Lazy/Strict
    val tpe = openImplicitTpeParam.getOrElse(weakTypeOf[T])
    val mapp = state.cache.asInstanceOf[Map[Type, List[(Type, Tree)]]]

    var typeConst = tpe
    while (typeConst.typeArgs.size == 1) typeConst = typeConst.typeArgs.head
    if (typeConst.takesTypeArgs) typeConst = typeConst.typeConstructor

    val analogConst = mapp.keySet.find(_ =:= typeConst)
    val list = analogConst
      .map(x => mapp.getOrElse(x, List.empty))
      .getOrElse(List.empty)

    val treeOpt = list.collectFirst {
      case (eTpe, eTree) if eTpe =:= tpe => eTree
    }

    treeOpt match {
      case Some(EmptyTree) =>
        state.hitn += 1
        c.info(c.enclosingPosition, s"HP/HN/M: ${state.hitp}/${state.hitn}/${state.misses}", force = forced)
        c.abort(c.enclosingPosition, s"Implicit $tpe not found")
      case Some(value) =>
        state.hitp += 1
        c.info(c.enclosingPosition, s"HP/HN/M: ${state.hitp}/${state.hitn}/${state.misses}", force = forced)
        q"_root_.shapeless.Cached2(${deepCopyTree(value)})"
      case None =>
        state.misses += 1
        c.info(c.enclosingPosition, s"HP/HN/M: ${state.hitp}/${state.hitn}/${state.misses}", force = forced)
        val tree0 = {
          if (tpe <:< weakTypeOf[<:!<[_, _]]) {
            val tp1 = tpe.typeArgs(0).dealias
            val tp2 = tpe.typeArgs(1).dealias
            if (tp1 <:< tp2) EmptyTree
            else c.inferImplicitValue(tpe)
          } else if(tpe <:< weakTypeOf[Option[_]]) {
            val tp = tpe.typeArgs.head
            val e = c.inferImplicitValue(tp)
            if(e == EmptyTree) q"None"
            else q"Some($e)"
          } else {
            c.inferImplicitValue(tpe)
          }
        }
        state.cache = state.cache.updated(analogConst getOrElse typeConst, (tpe, tree0) :: list)
        if (tree0 == EmptyTree)
          c.abort(c.enclosingPosition, s"Implicit $tpe not found")
        q"_root_.shapeless.Cached2($tree0)"
    }
  }
}

