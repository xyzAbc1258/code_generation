package bshapeless

import shapeless._

import scala.reflect.macros.blackbox

trait CommonTypes {
  this: MGenerator.MacroImpl =>

  val c: blackbox.Context
  import c.universe._

  object Func1Extractor {
    @inline def isFunc1(t: Type): Boolean = {
      val dealiased = t.dealias
      dealiased.typeArgs.size == 2 && dealiased <:< Types.funcType
    }

    def unapply(x: Type): Option[(Type, Type)] = {
      if (isFunc1(x)) Some((x.dealias.typeArgs.head, x.dealias.typeArgs(1)))
      else None
    }
  }


  case class Candidate(tree: Tree, size: Int)

  implicit val liftCandidate: Liftable[Candidate] = (c: Candidate) => c.tree


  sealed trait Args {
    def wholeTypeTree: Tree = TypeTree(wholeType)

    def wholeType: Type
  }

  case class SingleArg(t: Type) extends Args {
    override def wholeType: Type = t
  }

  case class ListArgs(t: Seq[Args]) extends Args {
    override def wholeType: c.universe.Type =
      t.map(_.wholeType).foldRight(Types.hnilType) {
        _ :::: _
      }
  }

  case class CoproductArgs(t: Seq[Args]) extends Args {
    override def wholeType: c.universe.Type =
      t.map(_.wholeType).foldRight(Types.cnilType) {
        _ +:+: _
      }
  }

  sealed trait Func {
    def args: Seq[Type]

    def result: Type

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate

    def withIndex(n: Int): Func

    def idx: Int //Index of function in context HList

    def subIndex: Int //Index of intersection part

    def incIdx: Func = withIndex(idx + 1)

    def wholeTypeTree: Tree = TypeTree(wholeType)

    def wholeType: Type
  }

  case class SimpleFunc(arg: Type, result: Type, idx: Int, subIndex: Int) extends Func {
    def args: Seq[Type] = Seq(arg)

    override def withIndex(n: Int): SimpleFunc = copy(idx = n)

    override def wholeType: c.universe.Type = arg ==> result

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate = {
      trees match {
        case Seq(ar) => ExprCreate.applyExpr(funcTree, ar, TypeTree(arg), TypeTree(result))
        case _ => sys.error("Incorrect number of arguments")
      }
    }
  }

  case class ComplexFunc(arg: Type, inner: Func, idx: Int, subIndex: Int) extends Func {
    def args: Seq[Type] = arg +: inner.args

    def result: Type = inner.result

    override def withIndex(n: Int): ComplexFunc = copy(inner = inner.withIndex(n), idx = n)

    override def wholeType: c.universe.Type = arg ==> inner.wholeType

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate = {
      trees match {
        case h +: t => inner(ExprCreate.applyExpr(funcTree, h, TypeTree(arg), inner.wholeTypeTree), t)
        case Seq() => sys.error("Incorrect number of arguments. Too small")
      }
    }
  }

  case class GenericFunction(genericArgs: Seq[Type], func: Func) extends Func {
    override def args: Seq[c.universe.Type] = func.args

    override def result: c.universe.Type = func.result

    override def withIndex(n: Int): Func = copy(func = func.withIndex(n))

    override def idx: Int = func.idx

    override def subIndex: Int = func.subIndex

    override def wholeType: c.universe.Type = func.wholeType

    c.typecheck()
  }

  def typeToFunc(t: Type, idx: Int, subIndex: Int = 0): List[Func] = {
    t.dealias match {
      case Func1Extractor(arg, r@Func1Extractor(_, _)) => List(ComplexFunc(arg, typeToFunc(r, idx).head, idx, subIndex))
      case Func1Extractor(arg, t) => List(SimpleFunc(arg, t, idx, subIndex))
      case RefinedType(inner, _) => inner.zipWithIndex.flatMap { case (t, i) => typeToFunc(t, idx, i) }
    }
  }

  def split2ArgsRec(t: Type, connectType: Type): List[Type] = {
    var tt = t.dealias
    var s = List[Type]()
    while (tt <:< connectType) {
      s = tt.typeArgs.head +: s
      tt = tt.typeArgs(1).dealias
    }
    s.reverse
  }

  def argsFromA(a: Type): Args = {
    if (a <:< weakTypeOf[Coproduct]) CoproductArgs(split2ArgsRec(a, Types.cconsType).map(argsFromA))
    else if (a <:< weakTypeOf[HList]) ListArgs(split2ArgsRec(a, Types.hconsType).map(argsFromA))
    else SingleArg(a)
  }

  def toInt[L <: Nat : c.WeakTypeTag]: Int = {
    var t = weakTypeOf[L].dealias
    var i = 0
    while (t <:< weakTypeOf[Succ[_]]) {
      t = t.typeArgs.head.dealias
      i += 1
    }
    i
  }

  def funcsFromCtx(t: Type): List[Func] = {
    val types = split2ArgsRec(t, Types.hconsType)
    types.zipWithIndex.flatMap((typeToFunc(_: Type, _: Int)).tupled)
  }


  def createContext[L <: Nat : c.WeakTypeTag, N <: Nat : c.WeakTypeTag,
    C <: HList : c.WeakTypeTag,
    A: c.WeakTypeTag,
    T: c.WeakTypeTag]: ExecCtx = {
    ExecCtx(
      toInt[N],
      funcsFromCtx(weakTypeTag[C].tpe.dealias),
      argsFromA(weakTypeTag[A].tpe.dealias),
      weakTypeTag[T].tpe.dealias,
      toInt[L]
    )
  }

  case class ExecCtx(
                      n: Int,
                      ctx: List[Func],
                      args: Args,
                      result: Type,
                      limit: Int
                    ) {

    def zeroed: ExecCtx = copy(n = 0)

    def decreaseN: ExecCtx = {
      if (n > 0) withN(n - 1)
      else sys.error(s"Cannot decrease $n")
    }

    def withN(t: Int): ExecCtx = copy(n = t)

    def withCtx(t: List[Func]): ExecCtx = copy(ctx = t)

    def withArgs(t: Args): ExecCtx = copy(args = t)

    def withResult(t: Type): ExecCtx = copy(result = t)

    def ctxTree: Tree = TypeTree(ctxType)

    def ctxType: Type = {
      ctx.groupBy(_.idx).map[(Int, Type)] { case (i, f) =>
        i -> (if (f.size == 1) f.head.wholeType else internal.intersectionType(f.map(_.wholeType)))
      }.toList.sortBy(_._1).map(_._2).foldRight(Types.hnilType) {
        _ :::: _
      }
    }

    def argTypeTree: Tree = args.wholeTypeTree

    def argType: Type = args.wholeType
  }


}
