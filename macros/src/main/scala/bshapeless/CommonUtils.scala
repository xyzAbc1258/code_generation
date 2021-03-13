package bshapeless

import scala.annotation.tailrec
import scala.reflect.macros.blackbox

trait CommonUtils {
  type U <: scala.reflect.api.Universe
  val u: U
  val c: blackbox.Context

  import u._

  def log(msg: String, force: Boolean = true): Unit = Option(c).foreach(x => x.info(x.enclosingPosition, msg, force = force))

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

    final def size(t: Type): Int = Timer.timer("Type size mesaure") {
      sizer(t)
    }

    @tailrec
    private final def sizer(t: Type, r: Seq[Type] = Nil, im: Int = 0): Int = {
      if (t.typeArgs.nonEmpty) {
        sizer(t.typeArgs.head.dealias, t.typeArgs.tail ++ r, im + 1)
      } else {
        if (r.isEmpty) im + 1
        else sizer(r.head.dealias, r.tail, im + 1)
      }
    }
  }

  object Timer extends TimerCollector

  implicit class CommonTypeBuilder(a2: Type) {
    private def apply(tycon: Type, args: Type*): Type = {
      appliedType(tycon, args.toList)
    }

    private def isSubType(t: Type, expected: Type): Boolean =
      t <:< expected

    def ::::(a1: Type): Type = { //Methods ending with colon bind to right eg. t1 :::: t2 == t2.::::(t1)
      assert(isSubType(a2, Types.hlistType), a2)
      apply(Types.hconsType.typeConstructor, a1, a2)
    }

    def +:+:(a1: Type): Type = {
      assert(isSubType(a2, Types.coproductType))
      appliedType(Types.cconsType.typeConstructor, a1, a2)
    }

    def ==>(a1: Type): Type = appliedType(Types.funcType.typeConstructor, a2, a1)

    def collect: Set[Type] = {
      val c = scala.collection.mutable.ListBuffer.empty[Type]
      a2.foreach(c.append)
      c.toSet
    }
  }

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

  /*Class that doesnt care about content. Useful in case classes to not care about element*/
  class AllEqualWrapper[T](val t: T) {

    override def hashCode(): Int = 0

    override def equals(o: Any): Boolean = o match {
      case _ : AllEqualWrapper[T]@unchecked => true
      case _ => false
    }
  }

  object AllEqualWrapper {
    def apply[T](t: T): AllEqualWrapper[T] = new AllEqualWrapper[T](t)
  }
}
