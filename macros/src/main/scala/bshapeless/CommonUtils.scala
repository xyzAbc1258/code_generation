package bshapeless

import scala.reflect.macros.blackbox

trait CommonUtils {
  val c: blackbox.Context
  import c.universe._

  def log(msg: String, force: Boolean = true): Unit = c.info(c.enclosingPosition, msg, force = force)

  object Types {
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

    def split2ArgsRec(t: Type, connectType: Type): List[Type] = {
      var tt = t.dealias
      var s = List[Type]()
      while (tt <:< connectType) {
        s = tt.typeArgs.head +: s
        tt = tt.typeArgs(1).dealias
      }
      s.reverse
    }
  }

  object Timer extends TimerCollector

  implicit class CommonTypeBuilder(a2: Type) {
    private def apply(tycon: c.universe.Type, args: c.universe.Type*): c.universe.Type = {
      appliedType(tycon, args.toList)
    }

    private def applyType(tycon: c.universe.Type, args: c.universe.Type*): c.universe.Type =
      apply(tycon, args: _*)

    private def isSubType(t: c.universe.Type, expected: c.universe.Type): Boolean =
      t <:< expected

    def ::::(a1: Type): Type = { //Methods ending with colon bind to right eg. t1 :::: t2 == t2.::::(t1)
      assert(isSubType(a2, Types.hlistType), a2)
      applyType(Types.hconsType.typeConstructor, a1, a2)
    }

    def +:+:(a1: Type): Type = {
      assert(isSubType(a2, Types.coproductType))
      applyType(Types.cconsType.typeConstructor, a1, a2)
    }

    def ==>(a1: Type): Type = applyType(Types.funcType.typeConstructor, a2, a1)

    def collect: Set[Type] = {
      val c = scala.collection.mutable.ListBuffer.empty[Type]
      a2.foreach(c.append)
      c.toSet
    }
  }

  object Func1Extractor {
    @inline def isFunc1(t: Type): Boolean = {
      val dealiased = t.dealias.dealias
      dealiased.typeArgs.size == 2 && dealiased <:< Types.funcType
    }

    def unapply(x: Type): Option[(Type, Type)] = {
      if (isFunc1(x)) Some((x.dealias.typeArgs.head, x.dealias.typeArgs(1)))
      else {
        None
      }
    }
  }

  def userMethods(tpe: Type): List[MethodSymbol] = {
    val allMethods = tpe.decls.collect{case x: MethodSymbol if !x.isConstructor && x.isPublic => x}
    if(tpe.typeSymbol.isClass && tpe.typeSymbol.asClass.isCaseClass) {
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
