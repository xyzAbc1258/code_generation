package bshapeless

import bshapeless.utils.CommonTypeOps

import scala.reflect.macros.blackbox

trait CommonUtils {
  type U <: scala.reflect.api.Universe
  val u: U
  val c: blackbox.Context

  import u._

  def log(msg: String, force: Boolean = true): Unit = Option(c).foreach(x => x.info(x.enclosingPosition, msg, force = force))

  object Types extends utils.Types[u.type](u) {
    override final def size(t: Type): Int = Timer.timer("Type size mesaure") {
      super.size(t)
    }
  }

  object Timer extends TimerCollector

  implicit def toCommonOps(t: Type): utils.CommonTypeOps[u.type] = new CommonTypeOps[u.type]((u, t, Types))

  object Func1Extractor {
    @inline def isFunc1(t: Type): Boolean = {
      val dealiased = t.dealias.dealias
      dealiased.typeArgs.size == 2 && dealiased.typeConstructor =:= Types.funcType.typeConstructor
    }

    def unapply(x: Type): Option[(Type, Type)] = {
      if (isFunc1(x)) Some((x.dealias.typeArgs.head, x.dealias.typeArgs(1)))
      else {
        None
      }
    }
  }

  object LabeledExtractor {
    val typ = weakTypeOf[shapeless.labelled.KeyTag[_, _]]

    def unapply(x: Type): Option[(Any, Type)] = {
      if (x <:< typ) {
        val asClass = typ.typeSymbol.asClass
        val labelSymbol = asClass.typeParams(0).asType.toType
        val innerSymbol = asClass.typeParams(1).asType.toType
        val labelType = labelSymbol.asSeenFrom(x, asClass)
        val innerType = innerSymbol.asSeenFrom(x, asClass)
        labelType match {
          case ConstantType(Constant(v)) => Some((v, innerType))
          case x => Some((x.toString, innerType))
        }
      }
      else None
    }

  }

  def userMethods(tpe: Type): List[MethodSymbol] = {
    val allMethods = tpe.decls.collect {
      case x: MethodSymbol if !x.isConstructor && x.isPublic => x
    }
    if (tpe.typeSymbol.isClass && tpe.typeSymbol.asClass.isCaseClass) {
      val excluded = weakTypeOf[Product].members.map(_.name).toSet[Name]
      val woExcluded = allMethods.filterNot(x => excluded(x.name))
      val woCopy = woExcluded.filterNot(x => x.name.decodedName.toString.startsWith("copy"))
      woCopy.toList
    } else {
      val excludedNames = Set("equals", "hashCode", "toString")
      allMethods.filterNot(x => excludedNames(x.name.decodedName.toString)).toList
    }
  }

}
