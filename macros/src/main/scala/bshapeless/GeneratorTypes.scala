package bshapeless

import shapeless.HList

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec

trait GeneratorTypes extends CommonUtils {

  import c.universe._

  //Lightweight representation of tree structure
  trait StructureTree

  object StructureTree {
    case object HNilTree extends StructureTree
    case class HListResult(head: StructureTree, tail: StructureTree) extends StructureTree

    case class CNilArg(tpe: String) extends StructureTree
    case class CoproductArgs(head: StructureTree, tail: StructureTree) extends StructureTree

    case class SelectArgs(n: Int) extends StructureTree

    case class FromArgsEq(tpe: String) extends StructureTree

    case class SelectCtx(n: Int) extends StructureTree

    case class Apply(fun: StructureTree, arg: StructureTree) extends StructureTree

    case class ApplyNative(name: String, arg: StructureTree) extends StructureTree

    case class Pair(first: StructureTree, second: StructureTree) extends StructureTree

    case class AbstractVal(inner: StructureTree) extends StructureTree

    case class AbstractFun(inner: StructureTree) extends StructureTree

    case class InlResult(inner: StructureTree) extends StructureTree

    case class InrResult(inner: StructureTree) extends StructureTree
  }

  object ExprCreate {

    def const(n: Int): Tree = Literal(Constant(n))

    def resType(implicit ctx: ExecCtx): Type = ctx.result

    def ttr(t: Type): Tree = TypeTree(t)

    def ctxTypeT(implicit ctx: ExecCtx): Tree = TypeTree(ctx.ctxType)

    def argTypeT(implicit ctx: ExecCtx): Tree = TypeTree(ctx.argType)

    def resTypeT(implicit ctx: ExecCtx): Tree = ttr(ctx.result)

    def hnil(implicit ctx: ExecCtx): Candidate =
      Candidate(q"HNilCreate.apply[$ctxTypeT, $argTypeT]", StructureTree.HNilTree)(ctx.withResult(Types.hnilType))

    def hList(head: Candidate, tail: Candidate, hType: Tree, tType: Tree)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"HListResultSplit[$ctxTypeT, $argTypeT, $hType, $tType]($head, $tail)",
        StructureTree.HListResult(head, tail),
        head, tail
      )

    def cnil(implicit ctx: ExecCtx): Candidate =
      Candidate(q"CNilCreate.apply[$ctxTypeT, $resTypeT]", StructureTree.CNilArg(resType.typeSymbol.name.decodedName.toString))(ctx.provider.withArg(Types.cnilType))

    def coproduct(h: Candidate, t: Candidate, hType: Type, tType: Type)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"CoproductArgSplit[$ctxTypeT, ${ttr(hType)}, ${ttr(tType)}, $resTypeT]($h, $t)",
        StructureTree.CoproductArgs(h, t),
        h, t
      )(ctx.provider.withArg(hType +:+: tType))

    def fromArgsSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
      Candidate(q"FromArgsSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})", StructureTree.SelectArgs(n))

    def fromArgsEq(implicit ctx: ExecCtx): Candidate =
      Candidate(q"FromArgsEq.create[$ctxTypeT, $argTypeT, $resTypeT]",
        StructureTree.FromArgsEq(resType.typeSymbol.name.decodedName.toString))

    def fromCtxSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
      Candidate(q"FromCtxSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})", StructureTree.SelectCtx(n))

    def applyExpr(funTree: Candidate, argTree: Candidate, imType: Tree, resultType: Tree)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"Apply[$ctxTypeT, $argTypeT, $imType, $resultType]($funTree, $argTree)",
        StructureTree.Apply(funTree, argTree),
        funTree, argTree
      )

    def applyNative(exTree: Candidate, fun: Tree, name: String)(implicit ctx: ExecCtx): Candidate =
      Candidate(q"ApplyNative($exTree, $fun, $name)", StructureTree.ApplyNative(name, exTree), exTree)

    def pair(a: Candidate, b: Candidate)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"PairExp[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($a, $b)",
        StructureTree.Pair(a, b),
        a, b
      )

    def abstractVal(e: Candidate)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"AbstractVal[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
        StructureTree.AbstractVal(e),
        e
      )


    def abstractValNotH(e: Candidate)(implicit ctx: ExecCtx): Candidate = Candidate(
      q"AbstractValNotH[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
      StructureTree.AbstractVal(e),
      e
    )

    def abstractFunc(e: Candidate)(implicit ctx: ExecCtx): Candidate = Candidate(
      q"AbstractFunc[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
      StructureTree.AbstractFun(e),
      e
    )

    def withMapCtx(f: Tree, e: Tree)(implicit ctx: ExecCtx): Tree =
      q"WithMapCtx($f, $e)"

    def inlResult(e: Candidate)(implicit ctx: ExecCtx): Candidate = {
      Candidate(
        q"InlResultExpr[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${
          ttr {
            resType.typeArgs(1)
          }
        }]($e)",
        StructureTree.InlResult(e),
        e
      )
    }

    def inrResult(e: Candidate)(implicit ctx: ExecCtx): Candidate = {
      Candidate(
        q"InrResultExpr[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${
          ttr {
            resType.typeArgs(1)
          }
        }]($e)",
        StructureTree.InrResult(e),
        e)
    }
  }

  case class Candidate private(tree: Tree, no: Int, dependencies: Seq[Candidate], structure: StructureTree, ec: GenCtxTpeProvider) {
    def term: Tree = q"$termName"

    val size: Int = dependencies.map(_.size).sum + 1

    def tpt: Tree = TypeTree(
      appliedType(
        weakTypeOf[bshapeless.exprs.Expr[_, _, _]].typeConstructor,
        ec.ctxType,
        ec.argType,
        ec.resType
      )
    )

    def valDef: ValDef = ValDef(NoMods, termName, tpt, tree)

    def termName: TermName = TermName("term_" + no)

    def allDependencies: Set[Candidate] = (dependencies ++ dependencies.flatMap(_.allDependencies)).toSet

    def allDepesWithItself: Set[Candidate] = allDependencies + this

    override def hashCode(): Int = no

    override def equals(o: Any): Boolean = o.isInstanceOf[Candidate] && (this eq o.asInstanceOf[Candidate])

  }

  object Candidate {

    class TreeShort(val provider: GenCtxTpeProvider, val structureTree: StructureTree) {
      override def equals(o: Any): Boolean = o match {
        case tt: TreeShort =>
          provider.resType =:= tt.provider.resType &&
          provider.ctxType =:= tt.provider.ctxType &&
          provider.argType =:= tt.provider.argType &&
            structureTree == tt.structureTree
      }

      override def hashCode(): Int = provider.resType.typeSymbol.name.decodedName.toString.hashCode
    }

    private val _counter: AtomicInteger = new AtomicInteger(0)

    private def next: Int = _counter.getAndIncrement()

    private val m: scala.collection.mutable.Map[TreeShort, Candidate] =
      scala.collection.mutable.Map.empty

    def apply(tree: Tree, structTree: StructureTree, dependencies: Candidate*)(implicit ec: GenCtxTpeProvider): Candidate = {
      Timer.timer("Candidate creator") {
        m.getOrElseUpdate(new TreeShort(ec, structTree), new Candidate(tree, next, dependencies, structTree, ec))
      }
    }

    implicit val liftCandidate: Liftable[Candidate] = (c: Candidate) => c.term
  }

  implicit def toStructureTree(c: Candidate): StructureTree = c.structure

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

  trait Indexed[T] {
    def idx: Int

    def subIndex: Int

    def withIndex(n: Int): T

    def incIdx(): T = withIndex(idx + 1)
  }

  trait FuncProvider extends Indexed[FuncProvider] {
    def fittingFunction(expectedResult: Type): Option[Func]

    def wholeType: Type
  }

  case class SimpleFuncProvider(f: Func) extends FuncProvider {
    override def fittingFunction(expectedResult: c.universe.Type): Option[Func] =
      Some(f).filter(_.result <:< expectedResult)

    override def wholeType: c.universe.Type = f.wholeType

    override def idx: Int = f.idx

    override def subIndex: Int = f.subIndex

    override def withIndex(n: Int): FuncProvider = copy(f.withIndex(n))
  }

  case class GenericFuncProvider(wholeType: Type, symbols: List[Type], idx: Int, subIndex: Int) extends FuncProvider {
    private val genType = typeToFunc(wholeType, idx, subIndex).head

    @tailrec
    private def compareSingle(s: Type, pt: Type, e: Type): Option[Type] = {
      //log(s"Attempt to unify: $pt and $e")
      if (pt.typeArgs.nonEmpty && e.typeArgs.nonEmpty) {
        if (pt.typeConstructor =:= e.typeConstructor) {
          (pt.typeArgs, e.typeArgs) match {
            case (a :: Nil, b :: Nil) => compareSingle(s, a, b)
            case (a1 :: a2 :: Nil, b1 :: b2 :: Nil) =>
              if(a1.contains(s.typeSymbol)) compareSingle(s, a1, b1)
              else compareSingle(s, a2, b2)
            case (a1 :: a2 :: a3 :: Nil, b1 :: b2 :: b3 :: Nil) =>
              if(a1.contains(s.typeSymbol)) compareSingle(s, a1, b1)
              else if(a2.contains(s.typeSymbol)) compareSingle(s, a2, b2)
              else compareSingle(s, a3, b3)
            case (pta, ea) =>
              pta.zip(ea).find(_._1.contains(s.typeSymbol)) match {
                case Some((pp, ep)) => compareSingle(s, pp, ep)
                case None =>None
              }
          }
        }
        else None
      } else if (pt <:< s)
        Some(e)
      else None
    }


    override def fittingFunction(expectedResult: c.universe.Type): Option[Func] = {
      val cand = symbols.map(x => compareSingle(x, genType.result, expectedResult.dealias))
      if (cand.exists(_.isEmpty)) return None
      val pairs = symbols zip cand.map(_.get)
      val tt = wholeType.map(x => pairs.find(_._1 =:= x).map(_._2).getOrElse(x))
      val gf = typeToFunc(tt, idx).head
      //log(s"Generic candidate. cands: $cand exp: $expected, got:  $tt")
      Some(gf).filter(_.result <:< expectedResult)
    }

    override def withIndex(n: Int): FuncProvider = copy(idx = n)
  }

  sealed trait Func extends Indexed[Func] {

    def args: Seq[Type]

    def result: Type

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate

    def wholeTypeTree: Tree = TypeTree(wholeType)

    def wholeType: Type
  }

  case class SimpleFunc(arg: Type, result: Type, idx: Int, subIndex: Int) extends Func {
    def args: Seq[Type] = Seq(arg)

    override def withIndex(n: Int): SimpleFunc = copy(idx = n)

    override def wholeType: c.universe.Type = arg ==> result

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate =
      trees match {
        case Seq(ar) => ExprCreate.applyExpr(funcTree, ar, TypeTree(arg), TypeTree(result))(ctx.withResult(result))
        case _ => sys.error("Incorrect number of arguments")
      }
  }

  case class ComplexFunc(arg: Type, inner: Func, idx: Int, subIndex: Int) extends Func {
    def args: Seq[Type] = arg +: inner.args

    def result: Type = inner.result

    override def withIndex(n: Int): ComplexFunc = copy(inner = inner.withIndex(n), idx = n)

    override def wholeType: c.universe.Type = arg ==> inner.wholeType

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate =
      trees match {
        case h +: t => inner(ExprCreate.applyExpr(funcTree, h, TypeTree(arg), inner.wholeTypeTree)(ctx.withResult(inner.wholeType)), t)
        case Seq() => sys.error("Incorrect number of arguments. Too small")
      }
  }

  def typeToFuncProvider(t: Type, idx: Int, subIndex: Int = 0): List[FuncProvider] = {
    t.dealias match {
      case t@Func1Extractor(_, _) if t.find(_ <:< Types.varType).isDefined =>
        List(GenericFuncProvider(t, t.collect.filter(_ <:< Types.varType).toList, idx, subIndex))
      case t => typeToFunc(t, idx, subIndex).map(SimpleFuncProvider)
    }
  }

  def typeToFunc(t: Type, idx: Int, subIndex: Int = 0): List[Func] = {
    t.dealias match {
      case Func1Extractor(arg, r@Func1Extractor(_, _)) =>
        List(ComplexFunc(arg, typeToFunc(r, idx).head, idx, subIndex))
      case Func1Extractor(arg, t) =>
        List(SimpleFunc(arg, t, idx, subIndex))
      case RefinedType(inner, _) =>
        inner.zipWithIndex.flatMap { case (t, i) => typeToFunc(t, idx, i) }
      case x => sys.error("Match error " + x)
    }
  }

  def argsFromA(a: Type): Args = {
    if (a <:< Types.coproductType) CoproductArgs(Types.split2ArgsRec(a, Types.cconsType).map(argsFromA))
    else if (a <:< Types.hlistType) ListArgs(Types.split2ArgsRec(a, Types.hconsType).map(argsFromA))
    else SingleArg(a)
  }

  def toInt[L <: shapeless.Nat : c.WeakTypeTag]: Int = {
    var t = weakTypeOf[L].dealias
    var i = 0
    while (t <:< Types.succType) {
      t = t.typeArgs.head.dealias
      i += 1
    }
    i
  }

  def funcsFromCtx(t: Type): List[FuncProvider] = {
    val types = Types.split2ArgsRec(t, Types.hconsType)
    types.zipWithIndex.flatMap((typeToFuncProvider(_: Type, _: Int)).tupled)
  }


  def createContext[L <: shapeless.Nat : c.WeakTypeTag, N <: shapeless.Nat : c.WeakTypeTag,
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
      Opts[O]
    )
  }

  case class TypeEqualityWrapper(t: Type) {
    override def equals(o: Any): Boolean = {
      o match {
        case TypeEqualityWrapper(tt) => t =:= tt
        case _ => false
      }
    }

    override def hashCode(): Int = 0
  }

  implicit def wrap(t: Type): TypeEqualityWrapper = TypeEqualityWrapper(t)

  implicit def unwrap(t: TypeEqualityWrapper): Type = t.t

  case class Opts(
    noLoops: Boolean
  )

  object Opts {
    def apply[O <: Options : c.WeakTypeTag]: Opts = Opts(weakTypeOf[O] <:< weakTypeOf[NoLoops])
  }


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
    ctx: List[FuncProvider],
    args: Args,
    resultT: TypeEqualityWrapper,
    limit: Int,
    options: Opts
  ) extends GenCtxTpeProvider {

    def result: Type = resultT.t

    def zeroed: ExecCtx = copy(n = 0)

    def decreaseN: ExecCtx = {
      if (n > 0) withN(n - 1)
      else sys.error(s"Cannot decrease $n")
    }

    def withN(t: Int): ExecCtx = copy(n = t)

    def withCtx(t: List[FuncProvider]): ExecCtx = copy(ctx = t)

    def withArgs(t: Args): ExecCtx = copy(args = t)

    def withResult(t: Type): ExecCtx = copy(resultT = t.dealias.map(_.dealias))

    def ctxType: Type = {
      ctx.groupBy(_.idx).map[(Int, Type)] { case (i, f) =>
        i -> (if (f.size == 1) f.head.wholeType else internal.intersectionType(f.map(_.wholeType)))
      }.toList.sortBy(_._1).map(_._2).foldRight(Types.hnilType) {
        _ :::: _
      }
    }

    def argType: Type = args.wholeType

    @inline val noLoops: Boolean = options.noLoops

    override def resType: c.universe.Type = result

    def provider: GenCtxTpeProvider.CustomGenCtxTpeProvider = GenCtxTpeProvider.derive(this)
  }

}
