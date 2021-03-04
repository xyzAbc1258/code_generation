package bshapeless

import shapeless.HList

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec

import scala.language.implicitConversions

trait GeneratorTypes extends CommonUtils {

  import c.universe._

  //Lightweight representation of tree structure
  sealed abstract class StructureTree(val treeName: String)

  object StructureTree {
    case class HNilTree(tpe: String) extends StructureTree(s"hnil $tpe")
    case class HListResult(head: StructureTree, tail: StructureTree) extends StructureTree("hcons")

    case class CNilArg(tpe: String) extends StructureTree(s"cnilArg $tpe")
    case class CoproductArgs(head: StructureTree, tail: StructureTree) extends StructureTree("cconsArg")

    case class SelectArgs(n: Int) extends StructureTree(s"selectArg $n")

    case class FromArgsEq(tpe: String) extends StructureTree(s"arg $tpe")

    case class SelectCtx(n: Int) extends StructureTree(s"selectCtx $n")

    case class Apply(fun: StructureTree, arg: StructureTree) extends StructureTree("apply")

    case class ApplyNative(name: String, arg: StructureTree) extends StructureTree(s"native $name")

    case class Pair(first: StructureTree, second: StructureTree) extends StructureTree("pair")

    case class AbstractVal(inner: StructureTree) extends StructureTree("abstractVal")

    case class AbstractFun(inner: StructureTree) extends StructureTree("abstractFun")

    case class InlResult(inner: StructureTree) extends StructureTree("inl")

    case class InrResult(inner: StructureTree) extends StructureTree("inr")
  }

  object ExprCreate {

    val ns = q"_root_.bshapeless.exprs"

    def const(n: Int): Tree = Literal(Constant(n))

    def resType(implicit ctx: ExecCtx): Type = ctx.result

    def ttr(t: Type): Tree = TypeTree(t)

    def ctxTypeT(implicit ctx: ExecCtx): Tree = TypeTree(ctx.ctxType)

    def argTypeT(implicit ctx: ExecCtx): Tree = TypeTree(ctx.argType)

    def resTypeT(implicit ctx: ExecCtx): Tree = ttr(ctx.result)

    def hnil(implicit ctx: ExecCtx): Candidate =
      Candidate(q"$ns.HNilCreate.apply[$ctxTypeT, $argTypeT]", StructureTree.HNilTree(ctx.argType.typeSymbol.name.decodedName.toString))(ctx.withResult(Types.hnilType))

    def hList(head: Candidate, tail: Candidate, hType: Tree, tType: Tree)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.HListResultSplit[$ctxTypeT, $argTypeT, $hType, $tType]($head, $tail)",
        StructureTree.HListResult(head, tail),
        head, tail
      )

    def cnil(implicit ctx: ExecCtx): Candidate =
      Candidate(q"$ns.CNilCreate.apply[$ctxTypeT, $resTypeT]", StructureTree.CNilArg(resType.typeSymbol.name.decodedName.toString))(ctx.provider.withArg(Types.cnilType))

    def coproduct(h: Candidate, t: Candidate, hType: Type, tType: Type)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.CoproductArgSplit[$ctxTypeT, ${ttr(hType)}, ${ttr(tType)}, $resTypeT]($h, $t)",
        StructureTree.CoproductArgs(h, t),
        h, t
      )(ctx.provider.withArg(hType +:+: tType))

    def fromArgsSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
      Candidate(q"$ns.FromArgsSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})", StructureTree.SelectArgs(n))

    def fromArgsEq(implicit ctx: ExecCtx): Candidate =
      Candidate(q"$ns.FromArgsEq.create[$ctxTypeT, $argTypeT, $resTypeT]",
        StructureTree.FromArgsEq(resType.typeSymbol.name.decodedName.toString))

    def fromCtxSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
      Candidate(q"$ns.FromCtxSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})", StructureTree.SelectCtx(n))

    def applyExpr(funTree: Candidate, argTree: Candidate, imType: Tree, resultType: Tree)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.Apply[$ctxTypeT, $argTypeT, $imType, $resultType]($funTree, $argTree)",
        StructureTree.Apply(funTree, argTree),
        funTree, argTree
      )

    def applyNative(exTree: Candidate, fun: Tree, name: String, member: Boolean)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.ApplyNative[$ctxTypeT, $argTypeT, ${TypeTree(exTree.ec.resType)}, $resTypeT]($exTree)($fun, $name, $member)",
        StructureTree.ApplyNative(name, exTree),
        exTree
      )

    def pair(a: Candidate, b: Candidate)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.PairExp[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($a, $b)",
        StructureTree.Pair(a, b),
        a, b
      )

    def abstractVal(e: Candidate)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.AbstractVal[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
        StructureTree.AbstractVal(e),
        e
      )


    def abstractValNotH(e: Candidate)(implicit ctx: ExecCtx): Candidate = Candidate(
      q"$ns.AbstractValNotH[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
      StructureTree.AbstractVal(e),
      e
    )

    def abstractFunc(e: Candidate)(implicit ctx: ExecCtx): Candidate = Candidate(
      q"$ns.AbstractFunc[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
      StructureTree.AbstractFun(e),
      e
    )

    def withMapCtx(f: Tree, e: Tree)(implicit ctx: ExecCtx): Tree =
      q"$ns.WithMapCtx($f, $e)"

    def inlResult(e: Candidate)(implicit ctx: ExecCtx): Candidate = {
      Candidate(
        q"$ns.InlResultExpr[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${
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
        q"$ns.InrResultExpr[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${
          ttr {
            resType.typeArgs(1)
          }
        }]($e)",
        StructureTree.InrResult(e),
        e)
    }
  }

  case class Candidate private(tree: Tree, no: Int, dependencies: Seq[Candidate], structure: StructureTree, ec: GenCtxTpeProvider) {
    def term: Tree = Ident(termName)

    val size: Int = dependencies.map(_.size).sum + 1

    lazy val tpt: Tree = TypeTree(
      appliedType(
        Candidate.exprTpe.typeConstructor,
        ec.ctxType,
        ec.argType,
        ec.resType
      )
    )

    def valDef: ValDef = ValDef(Candidate.mods, termName, tpt, tree)

    val termName: TermName = TermName("term_" + no)

    def allDependencies: Set[Candidate] = (dependencies ++ dependencies.flatMap(_.allDependencies)).toSet

    def allDepesWithItself: Set[Candidate] = allDependencies + this

    override def hashCode(): Int = no

    override def equals(o: Any): Boolean = o.isInstanceOf[Candidate] && (this eq o.asInstanceOf[Candidate])
  }

  object Candidate {
    private val mods = Modifiers(Flag.FINAL)
    private val exprTpe: Type = weakTypeOf[bshapeless.exprs.Expr[_, _, _]]

    case class TreeShort(treeName: String, depsNo: Seq[Int], provider: GenCtxTpeProvider.CustomGenCtxTpeProvider)

    private val _counter: AtomicInteger = new AtomicInteger(0)

    private def next: Int = _counter.getAndIncrement()

    private val m: scala.collection.mutable.Map[TreeShort, Candidate] =
      scala.collection.mutable.Map.empty

    def apply(tree: Tree, structTree: StructureTree, dependencies: Candidate*)(implicit ec: GenCtxTpeProvider): Candidate = {
      Timer.timer("Candidate creator") {
        m.getOrElseUpdate(
          TreeShort(structTree.treeName, dependencies.map(_.no), GenCtxTpeProvider.derive(ec)),
          new Candidate(tree, next, dependencies, structTree, ec)
        )
      }
    }

    implicit val liftCandidate: Liftable[Candidate] = (c: Candidate) => c.term
  }

  implicit def toStructureTree(c: Candidate): StructureTree = c.structure

  sealed trait Args {
    def wholeType: Type
  }

  case class SingleArg(wholeType: Type) extends Args

  case class ListArgs(t: Seq[Args], wholeTypeOpt: Option[Type] = None) extends Args {
    //wholeTypeOpt is an optimization. With "big" types they are often aliased,
    //and use of such aliases make compilation faster.
    //big types repeated many types are a lot of work to refcheck compilation phase

    @tailrec
    final def size(t: Type, r: Seq[Type] = Nil, im: Int = 0): Int = {
      if(t.typeArgs.nonEmpty){
        size(t.typeArgs.head.dealias, t.typeArgs.tail ++ r, im + 1)
      } else {
        if(r.isEmpty) im + 1
        else size(r.head.dealias, r.tail, im + 1)
      }
    }

    def prepend(newArgs: Args): ListArgs = {
      ListArgs(newArgs +: t, wholeTypeOpt.map(newArgs.wholeType :::: _))
    }

    private val groupBySize = scala.collection.immutable.IntMap.from(
      t.zipWithIndex
      .collect{case (SingleArg(t), i) => t -> i}
      .groupBy(x => size(x._1))
      .view.mapValues(_.toArray)
    )

    log(s"Arg map sizes: ${groupBySize.view.mapValues(_.length).mkString("\n")}")

    val wholeType: c.universe.Type = wholeTypeOpt getOrElse {
      t.map(_.wholeType).foldRight(Types.hnilType) {
        _ :::: _
      }
    }

    @inline
    def subTypeIndices(tpe: Type)(implicit ec: ExecCtx): Seq[Int] = {
      if(ec.noSubtyping)
        groupBySize.getOrElse(size(tpe), Array.empty[(Type, Int)]).filter(_._1 =:= tpe).map(_._2)
      else
        t.zipWithIndex.collect{case (SingleArg(t), i) if t <:< tpe => i}
    }
  }

  case class CoproductArgs(t: Seq[Args]) extends Args {
    lazy val wholeType: c.universe.Type =
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

  case class GenericFuncProvider(wholeType: Type, symbols: Map[Type, Set[Type]], idx: Int, subIndex: Int) extends FuncProvider {
    private val genType = typeToFunc(wholeType, idx, subIndex).head

    @tailrec
    private def compareSingle(s: Type, pt: Type, e: Type): Option[Type] = {
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
      val cand = symbols.keys.map(x => x -> compareSingle(x, genType.result, expectedResult.dealias))
      if (cand.exists(_._2.isEmpty)) return None
      val pairs = cand.collect{case (k, Some(v)) => symbols(k) -> v}
        .flatMap{x => x._1.map(a => a -> x._2)}.toArray
      val tt = wholeType.map(x => pairs.find(_._1 =:= x).map(_._2).getOrElse(x))
      val gf = typeToFunc(tt, idx).head
      //log(s"Generic candidate. cands: $cand exp: $expectedResult, got:  ${gf.result}")
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

  case class SimpleFunc1(arg: Type, result: Type, idx: Int, subIndex: Int) extends Func {
    def args: Seq[Type] = Seq(arg)

    override def withIndex(n: Int): SimpleFunc1 = copy(idx = n)

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

  case class ObjectFunc(wholeType: Type, objType: Type, method: MethodSymbol, idx: Int) extends Func {
    val inner = {
      if(method.paramLists.flatten.nonEmpty) {
        def buildT(args: List[List[Symbol]]): Type = args match {
          case List(s) :: tail => s.info ==> buildT(tail)
          case Nil => method.returnType
        }
        typeToFunc(buildT(method.paramLists), 0, 0).headOption
      } else None
    }

    override def args: Seq[c.universe.Type] = objType +: inner.map(_.args).getOrElse(Nil)

    override def result: c.universe.Type = inner.map(_.result).getOrElse(method.returnType)

    override def subIndex: Int = 0

    override def withIndex(n: Int): Func = copy(idx = n)

    override def apply(objTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate = {
      val h = trees.head
      if(inner.nonEmpty) {
        val funcTree = ExprCreate.applyNative(
          h,
          q"(x: ${TypeTree(objType)}) => (x.$method):${TypeTree(inner.get.wholeType)}",
          method.name.decodedName.toString,
          true
        )(ctx.withResult(inner.get.wholeType))
        inner.get(funcTree, trees.tail)
      } else {
        ExprCreate.applyNative(
          h,
          q"(x: ${TypeTree(objType)}) => x.$method",
          method.name.decodedName.toString,
          true
        )(ctx.withResult(result))
      }
    }
  }

  def typeToFuncProvider(t: Type, idx: Int, subIndex: Int = 0): List[FuncProvider] = {
    t.dealias match {
      case t@Func1Extractor(_, _) if t.find(_ <:< Types.varType).isDefined =>
        val varSymbols = t.collect.filter(_ <:< Types.varType)
        val basicTypes = varSymbols.filter(x => !(varSymbols - x).exists(y => x <:< y))
        val map = basicTypes.map(x => x -> varSymbols.filter(_ <:< x)).toMap
        List(GenericFuncProvider(t, map, idx, subIndex))
      case t => typeToFunc(t, idx, subIndex).map(SimpleFuncProvider)
    }
  }

  def typeToFunc(t: Type, idx: Int, subIndex: Int = 0): List[Func] = {
    t.dealias match {
      case Func1Extractor(arg, r@Func1Extractor(_, _)) =>
        List(ComplexFunc(arg, typeToFunc(r, idx).head, idx, subIndex))
      case Func1Extractor(arg, t) =>
        List(SimpleFunc1(arg, t, idx, subIndex))
      case RefinedType(inner, _) =>
        inner.zipWithIndex.flatMap { case (t, i) => typeToFunc(t, idx, i) }
      case t if t <:< Types.objectProviderTpe =>
        val tpe = t.typeArgs.head
        val methods = userMethods(tpe)
        log(s"Methods: ${methods.mkString("\n")}")
        methods.map(x => ObjectFunc(t, tpe, x, idx))
      case MethodType(_, tpe) => typeToFunc(tpe, idx, subIndex)
      case x => sys.error("Match error " + x + " " + showRaw(x))
    }
  }

  def argsFromA(a: Type): Args = {
    if (a <:< Types.coproductType) CoproductArgs(Types.split2ArgsRec(a, Types.cconsType).map(argsFromA))
    else if (a <:< Types.hlistType) ListArgs(Types.split2ArgsRec(a, Types.hconsType).map(argsFromA), Some(a))
    else SingleArg(a)
  }

  case class ContextFunctions(providers: List[FuncProvider], wholeTypeOpt: Option[Type]) {
    @inline
    private def intersect(t: List[Type]): Type = {
      t match {
        case List(t) => t
        case l if l.head.isInstanceOf[ObjectFunc] => l.head.asInstanceOf[ObjectFunc].objType
        case l => internal.intersectionType(l)
      }
    }

    def prepend(newProvider: List[FuncProvider]): ContextFunctions = {
      ContextFunctions(
        newProvider ++ providers.map(_.incIdx()),
        wholeTypeOpt.map(intersect(newProvider.map(_.wholeType)) :::: _)
      )
    }

    def wholeType: Type = wholeTypeOpt getOrElse {
      providers.groupBy(_.idx).map[(Int, Type)] { case (i, f) => i -> intersect(f.map(_.wholeType))
      }.toList.sortBy(_._1).map(_._2).foldRight(Types.hnilType) { _ :::: _ }
    }
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

  def funcsFromCtx(t: Type): ContextFunctions = {
    val types = Types.split2ArgsRec(t, Types.hconsType)
    ContextFunctions(types.zipWithIndex.flatMap((typeToFuncProvider(_: Type, _: Int)).tupled), Some(t))
  }


  def createContext[L <: shapeless.Nat : c.WeakTypeTag, N <: shapeless.Nat : c.WeakTypeTag,
    C <: HList : c.WeakTypeTag,
    A: c.WeakTypeTag,
    T: c.WeakTypeTag,
    O <: Options : c.WeakTypeTag]: ExecCtx = {
    ExecCtx(
      toInt[N],
      funcsFromCtx(weakTypeOf[C]),
      argsFromA(weakTypeOf[A]),
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

    override val hashCode: Int = t.typeSymbol.name.decodedName.hashCode()
  }

  implicit def wrap(t: Type): TypeEqualityWrapper = TypeEqualityWrapper(t)

  implicit def unwrap(t: TypeEqualityWrapper): Type = t.t

  case class Opts(
    noLoops: Boolean,
    noSubtyping: Boolean
  )

  object Opts {
    def apply[O <: Options : c.WeakTypeTag]: Opts = Opts(
      weakTypeOf[O] <:< weakTypeOf[NoLoops],
      weakTypeOf[O] <:< weakTypeOf[NoSubtyping]
    )
  }


  trait GenCtxTpeProvider {
    def ctxType: Type

    def argType: Type

    def resType: Type
  }

  object GenCtxTpeProvider {

    case class CustomGenCtxTpeProvider(ctxTypeT: TypeEqualityWrapper, argTypeT: TypeEqualityWrapper, resTypeT: TypeEqualityWrapper) extends GenCtxTpeProvider {

      def ctxType: Type = ctxTypeT
      def argType: Type = argTypeT
      def resType: Type = resTypeT

      def withCtx(ctx: Type): CustomGenCtxTpeProvider = copy(ctxTypeT = ctx)

      def withArg(arg: Type): CustomGenCtxTpeProvider = copy(argTypeT = arg)

      def withRes(res: Type): CustomGenCtxTpeProvider = copy(resTypeT = res)

      override val hashCode: Int = super.hashCode()
    }

    def apply(ctx: Type, arg: Type, res: Type): CustomGenCtxTpeProvider =
      CustomGenCtxTpeProvider(ctx, arg, res)

    def derive(tpeProvider: GenCtxTpeProvider): CustomGenCtxTpeProvider = {
      tpeProvider match {
        case provider: CustomGenCtxTpeProvider => provider
        case _ => apply(tpeProvider.ctxType, tpeProvider.argType, tpeProvider.resType)
      }
    }
  }

  case class ExecCtx(
    n: Int,
    ctx: ContextFunctions,
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

    def withCtx(f: ContextFunctions => ContextFunctions): ExecCtx = copy(ctx = f(ctx))

    def withArgs(t: Args): ExecCtx = copy(args = t)

    def withResult(t: Type): ExecCtx = copy(resultT = t.dealias.map(_.dealias))

    override val hashCode: Int = super.hashCode()

    def ctxType: Type = ctx.wholeType

    def argType: Type = args.wholeType

    @inline val noLoops: Boolean = options.noLoops
    @inline val noSubtyping: Boolean = options.noSubtyping

    override def resType: c.universe.Type = result

    def provider: GenCtxTpeProvider.CustomGenCtxTpeProvider = GenCtxTpeProvider.derive(this)
  }

}
