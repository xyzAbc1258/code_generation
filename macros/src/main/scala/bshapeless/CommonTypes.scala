package bshapeless

import shapeless._

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec
import scala.reflect.macros.blackbox

trait CommonTypes {

  val c: blackbox.Context

  import c.universe._

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

  object Types {
    val hnilType: Type = weakTypeOf[HNil]
    val cnilType: Type = weakTypeOf[CNil]
    val hconsType: Type = weakTypeOf[shapeless.::[_, _]]
    val cconsType: Type = weakTypeOf[:+:[_, _]]
    val funcType: Type = weakTypeOf[(_) => _]

    val varType: Type = weakTypeOf[Var]
  }

  trait Appliable[T] {
    def apply(tycon: T, args: T*): T

    def applyType(tycon: Type, args: T*): T

    def isSubType(t: T, expected: Type): Boolean
  }


  object Appliable {

    def apply[T](implicit e: Appliable[T]): Appliable[T] = e

    implicit val ApplicableType: Appliable[c.universe.Type] = new Appliable[Type] {
      override def apply(tycon: c.universe.Type, args: c.universe.Type*): c.universe.Type = {
        appliedType(tycon, args.toList)
      }

      override def applyType(tycon: c.universe.Type, args: c.universe.Type*): c.universe.Type =
        apply(tycon, args: _*)

      override def isSubType(t: c.universe.Type, expected: c.universe.Type): Boolean =
        t <:< expected
    }
  }

  implicit class TypeOps(a: Type) {
    def collect: Set[Type] = {
      val c = scala.collection.mutable.ListBuffer.empty[Type]
      a.foreach(c.append(_))
      c.toSet
    }
  }

  implicit class CommonTypeBuilder[T: Appliable](a2: T) {
    def ::::(a1: T): T = { //Methods ending with colon bind to right eg. t1 :::: t2 == t2.::::(t1)
      assert(Appliable[T].isSubType(a2, weakTypeOf[HList]), a2)
      Appliable[T].applyType(Types.hconsType.typeConstructor, a1, a2)
    }

    def +:+:(a1: T): T = {
      assert(Appliable[T].isSubType(a2, weakTypeOf[Coproduct]))
      Appliable[T].applyType(Types.cconsType.typeConstructor, a1, a2)
    }

    def ==>(a1: T): T =
      Appliable[T].applyType(Types.funcType.typeConstructor, a2, a1)
  }


  case class Candidate private(tree: Tree, size: Int, no: Int, dependencies: Seq[Candidate], ec: GenCtxTpeProvider) {
    def term: Tree = q"$termName"

    def tpt: Tree = TypeTree(
      appliedType(
        weakTypeOf[bshapeless.exprs.Expr[_,_,_]].typeConstructor,
        ec.ctxType,
        ec.argType,
        ec.resType
      )
    )

    def valDef: ValDef = ValDef(NoMods, termName, tpt, tree)

    def termName: TermName = TermName("term_" + no)

    def allDependencies: Set[Candidate] = (dependencies ++ dependencies.flatMap(_.allDependencies)).toSet

    def allDepesWithItself = allDependencies + this

    override def hashCode(): Int = no // no is unique by construction

    override def equals(o: Any): Boolean = o match {
      case o: Candidate => no == o.no
      case _ => false
    }

  }

  object Candidate {

    private val _counter: AtomicInteger = new AtomicInteger(0)

    private def next: Int = _counter.getAndIncrement()

    def apply(tree: Tree, dependencies: Candidate*)(implicit ec: GenCtxTpeProvider) =
      new Candidate(tree, dependencies.map(_.size).sum + 1 , next, dependencies, ec)
  }

  implicit val liftCandidate: Liftable[Candidate] = (c: Candidate) => c.term


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

    def resultFits(expected: Type): Option[Func]

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

  trait ExprCreator {
    def applyExpr(funTree: Candidate, argTree: Candidate, imType: Tree, resultType: Tree)(implicit ctx: ExecCtx): Candidate
  }

  val exprCreate: ExprCreator

  case class SimpleFunc(arg: Type, result: Type, idx: Int, subIndex: Int) extends Func {
    def args: Seq[Type] = Seq(arg)

    override def withIndex(n: Int): SimpleFunc = copy(idx = n)

    override def wholeType: c.universe.Type = arg ==> result

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate = {
      trees match {
        case Seq(ar) => exprCreate.applyExpr(funcTree, ar, TypeTree(arg), TypeTree(result))(ctx.withResult(result))
        case _ => sys.error("Incorrect number of arguments")
      }
    }

    override def resultFits(expected: c.universe.Type): Option[Func] = Some(this).filter(_ => result <:< expected)
  }

  case class ComplexFunc(arg: Type, inner: Func, idx: Int, subIndex: Int) extends Func {
    def args: Seq[Type] = arg +: inner.args

    def result: Type = inner.result

    override def withIndex(n: Int): ComplexFunc = copy(inner = inner.withIndex(n), idx = n)

    override def wholeType: c.universe.Type = arg ==> inner.wholeType

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate = {
      trees match {
        case h +: t => inner(exprCreate.applyExpr(funcTree, h, TypeTree(arg), inner.wholeTypeTree)(ctx.withResult(inner.wholeType)), t)
        case Seq() => sys.error("Incorrect number of arguments. Too small")
      }
    }

    override def resultFits(expected: c.universe.Type): Option[Func] = Some(this).filter(x => result <:< expected)
  }


    case class GenericFunction(wholeType: Type, symbols: List[Type], func: Type, idx: Int, subIndex: Int) extends Func {

      val genType = typeToFunc(func, idx, subIndex, true).head

      override def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate = ???

      override def args: Seq[c.universe.Type] = ???

      override def result: c.universe.Type = ???

      override def withIndex(n: Int): Func = copy(idx = n)

      override def resultFits(expected: c.universe.Type): Option[Func] = {
        @tailrec
        def compareSingle(s: Type, pt: Type, e: Type): Type = {
          c.info(c.enclosingPosition, s"Attempt to unify: $pt and $e", true)
          if(pt.typeArgs.nonEmpty && e.typeArgs.nonEmpty) {
            if(pt.typeConstructor =:= e.typeConstructor) {
              val ptArgsInd = pt.typeArgs.indexWhere(_.contains(s.typeSymbol))
              compareSingle(s, pt.typeArgs(ptArgsInd).dealias, e.typeArgs(ptArgsInd).dealias)
            }
            else e
          } else e
        }
        val cand = symbols.map(x => compareSingle(x, genType.result, expected.dealias))
        val pairs = symbols zip cand
        val tt = func.map(x => pairs.find(_._1 =:= x).map(_._2).getOrElse(x))
        val gf = typeToFunc(tt, idx).head
        c.info(c.enclosingPosition, s"Generic candidate. cands: $cand exp: $expected, got:  $tt", true)
        Some(gf).filter(_.result <:< expected)
      }
    }

  def typeToFunc(t: Type, idx: Int, subIndex: Int = 0, disableGeneric: Boolean = false): List[Func] = {
    t.dealias match {
      case t@Func1Extractor(_, _) if t.find(_ <:< Types.varType).isDefined && !disableGeneric =>
        List(GenericFunction(t, t.collect.filter(_ <:< Types.varType).toList, t, idx, subIndex))
      case Func1Extractor(arg, r@Func1Extractor(_, _)) => List(ComplexFunc(arg, typeToFunc(r, idx, disableGeneric = disableGeneric).head, idx, subIndex))
      case Func1Extractor(arg, t) => List(SimpleFunc(arg, t, idx, subIndex))
      case RefinedType(inner, _) => inner.zipWithIndex.flatMap { case (t, i) => typeToFunc(t, idx, i, disableGeneric = disableGeneric) }
      case x => sys.error("Match error " + x)
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
    T: c.WeakTypeTag,
    O <: Options : c.WeakTypeTag]: ExecCtx = {
    ExecCtx(
      toInt[N],
      funcsFromCtx(weakTypeTag[C].tpe.dealias),
      argsFromA(weakTypeTag[A].tpe.dealias),
      weakTypeTag[T].tpe.dealias,
      toInt[L],
      toOpts[O]
    )
  }

  case class TypeEqualityWrapper(t: Type) {
    override def equals(o: Any): Boolean = {
      o match {
        case TypeEqualityWrapper(tt) => t =:= tt
        case _ => false
      }
    }
  }

  implicit def wrap(t: Type): TypeEqualityWrapper = TypeEqualityWrapper(t)

  implicit def unwrap(t: TypeEqualityWrapper): Type = t.t

  case class Opts(
    noLoops: Boolean
  )

  def toOpts[O <: Options: c.WeakTypeTag]: Opts =
    Opts(weakTypeOf[O] <:< weakTypeOf[NoLoops])

  trait GenCtxTpeProvider {
    def ctxType: Type
    def argType: Type
    def resType: Type
  }

  object GenCtxTpeProvider {

    case class CustomGenCtxTpeProvider(ctxType: Type, argType: Type, resType: Type) extends GenCtxTpeProvider {
      def withCtx(ctx: Type): CustomGenCtxTpeProvider = copy(ctxType = ctx)
      def withArg(arg: Type): CustomGenCtxTpeProvider = copy(argType = arg)
      def withRes(res: Type): CustomGenCtxTpeProvider = copy(resType = res)
    }

    def apply(ctx: Type, arg: Type, res: Type): CustomGenCtxTpeProvider =
      CustomGenCtxTpeProvider(ctx, arg, res)

    def derive(tpeProvider: GenCtxTpeProvider): CustomGenCtxTpeProvider =
      apply(tpeProvider.ctxType, tpeProvider.argType, tpeProvider.resType)
  }

  case class ExecCtx(
    n: Int,
    ctx: List[Func],
    args: Args,
    resultT: TypeEqualityWrapper,
    limit: Int,
    options: Opts
  ) extends GenCtxTpeProvider {

    def result = resultT.t

    def zeroed: ExecCtx = copy(n = 0)

    def decreaseN: ExecCtx = {
      if (n > 0) withN(n - 1)
      else sys.error(s"Cannot decrease $n")
    }

    def withN(t: Int): ExecCtx = copy(n = t)

    def withCtx(t: List[Func]): ExecCtx = copy(ctx = t)

    def withArgs(t: Args): ExecCtx = copy(args = t)

    def withResult(t: Type): ExecCtx = copy(resultT = t.dealias.map(_.dealias))

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

    @inline val noLoops: Boolean = options.noLoops

    override def resType: c.universe.Type = result

    def provider: GenCtxTpeProvider.CustomGenCtxTpeProvider = GenCtxTpeProvider.derive(this)
  }


}
