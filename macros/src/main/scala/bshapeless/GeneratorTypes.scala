package bshapeless

import bshapeless.exprs.CNilCreate.CNilCreate
import bshapeless.exprs.ExprBuilderGeneric
import bshapeless.exprs.ExprTree
import bshapeless.exprs.ExprType
import bshapeless.exprs.HListResultSplit
import bshapeless.exprs.HNilCreate
import shapeless.HList

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec
import scala.collection.mutable
import scala.language.implicitConversions

trait GeneratorTypes extends CommonUtils {

  //import _

  import u._
  
  //Lightweight representation of tree structure
  sealed abstract class StructureTree(val treeName: String, val typ: ExprType) extends ExprTree {
    type ATT = StructureTree
    type W[_] = Tree
  }

  object StructureTree {

    case class HNilTree(tpe: String) extends StructureTree(s"hnil $tpe", ExprType.HNilTree) {
      override def build[R](b: Builder[R]): R = b.buildHNil
    }

    case class HListResult(head: StructureTree, tail: StructureTree) extends StructureTree("hcons", ExprType.HListResult) {
      override def build[R](b: Builder[R]): R = b.buildHList(head, tail)
    }

    case class CNilArg(tpe: String) extends StructureTree(s"cnilArg $tpe", ExprType.CNilArg) {
      override def build[R](b: Builder[R]): R = b.buildCNil
    }

    case class CoproductArgs(head: StructureTree, tail: StructureTree) extends StructureTree("cconsArg", ExprType.CoproductArgs) {
      override def build[R](b: Builder[R]): R = b.buildCoproduct(head, tail)
    }

    case class SelectArgs(n: Int) extends StructureTree(s"selectArg $n", ExprType.SelectArgs) {
      override def build[R](b: Builder[R]): R = b.buildSelectArg(n)
    }

    case class FromArgsEq(tpe: String) extends StructureTree(s"arg $tpe", ExprType.FromArgsEq) {
      override def build[R](b: Builder[R]): R = b.buildFromArg
    }

    case class SelectCtx(n: Int) extends StructureTree(s"selectCtx $n", ExprType.SelectCtx) {
      override def build[R](b: Builder[R]): R = b.buildSelectCtx(n)
    }

    case class Apply(fun: StructureTree, arg: StructureTree) extends StructureTree("apply", ExprType.Apply) {
      override def build[R](b: Builder[R]): R = b.buildApply(fun, arg)
    }

    case class ApplyNative(name: String, arg: StructureTree, f: AllEqualWrapper[Tree], asMember: Boolean = false) extends StructureTree(s"native $name", ExprType.ApplyNative) {
      override def build[R](b: Builder[R]): R = b.buildApplyNative(name, f.t, asMember, arg)
    }

    case class Pair(first: StructureTree, second: StructureTree) extends StructureTree("pair", ExprType.Pair) {
      override def build[R](b: Builder[R]): R = b.buildPair(first, second)
    }

    case class AbstractVal(inner: StructureTree, argIsHList: Boolean) extends StructureTree("abstractVal", ExprType.AbstractVal(argIsHList)) {
      override def build[R](b: Builder[R]): R = b.buildAbstractVal(inner)
    }

    case class AbstractFun(inner: StructureTree) extends StructureTree("abstractFun", ExprType.AbstractFun) {
      override def build[R](b: Builder[R]): R = b.buildAbstractFun(inner)
    }

    case class InlResult(inner: StructureTree) extends StructureTree("inl", ExprType.InlResult) {
      override def build[R](b: Builder[R]): R = b.buildInlResult(inner)
    }

    case class InrResult(inner: StructureTree) extends StructureTree("inr", ExprType.InrResult) {
      override def build[R](b: Builder[R]): R = b.buildInrResult(inner)
    }

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
        StructureTree.ApplyNative(name, exTree, AllEqualWrapper(fun), member),
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
        StructureTree.AbstractVal(e, true),
        e
      )


    def abstractValNotH(e: Candidate)(implicit ctx: ExecCtx): Candidate = Candidate(
      q"$ns.AbstractValNotH[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
      StructureTree.AbstractVal(e, false),
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

    private val m: scala.collection.mutable.AnyRefMap[TreeShort, Candidate] =
      scala.collection.mutable.AnyRefMap.empty

    def apply(tree: Tree, structTree: StructureTree, dependencies: Candidate*)(implicit ec: GenCtxTpeProvider): Candidate = {
      val derived = GenCtxTpeProvider.derive(ec)
      m.getOrElseUpdate(
        TreeShort(structTree.treeName, dependencies.map(_.no), derived),
        new Candidate(tree, next, dependencies, structTree, derived)
      )
    }

    implicit val liftCandidate: Liftable[Candidate] = (c: Candidate) => c.term
  }

  implicit def toStructureTree(c: Candidate): StructureTree = c.structure

  sealed trait Args {
    def wholeType: Type

    def name: Option[Any]

    lazy val wholeTypeWrapper: TypeEqualityWrapper = wholeType
  }

  case class SingleArg(wholeType: Type, name: Option[Any]) extends Args

  case class ListArgs(t: Seq[Args], wholeTypeOpt: Option[Type] = None) extends Args {
    //wholeTypeOpt is an optimization. With "big" types they are often aliased,
    //and use of such aliases make compilation faster.
    //big types repeated many types are a lot of work to refcheck compilation phase

    def name: Option[HList] = {
      val nn = t.map(_.name)
      if(nn.forall(_.isDefined)) {
        Some(nn.map(_.get).foldRight[HList](shapeless.HNil)(_ :: _))
      } else None
    }

    def prepend(newArgs: Args): ListArgs = {
      ListArgs(newArgs +: t, wholeTypeOpt.map(newArgs.wholeType :::: _))
    }

    private val groupBySize = scala.collection.immutable.IntMap.from(
      t.zipWithIndex
        .collect { case (SingleArg(t, _), i) => t -> i }
        .groupBy(x => Types.size(x._1))
        .view.mapValues(_.toArray)
    )

    log(s"Arg map sizes: ${groupBySize.view.mapValues(_.length).mkString("\n")}")

    val wholeType: Type = wholeTypeOpt getOrElse {
      t.map(_.wholeType).foldRight(Types.hnilType) {
        _ :::: _
      }
    }

    @inline
    def subTypeIndices(tpe: Type)(implicit ec: ExecCtx): Seq[Int] = {
      if (ec.noSubtyping)
        groupBySize.getOrElse(Types.size(tpe), Array.empty[(Type, Int)]).filter(_._1 =:= tpe).map(_._2)
      else
        t.zipWithIndex.collect { case (SingleArg(t, _), i) if t <:< tpe => i }
    }
  }

  case class CoproductArgs(t: Seq[Args], name: Option[Any]) extends Args {
    lazy val wholeType: Type =
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
    def fittingFunction(expectedResult: Type)(implicit e: ExecCtx): Option[Func]

    def wholeType: Type

    def name: Option[String]

    def withName(n: String): FuncProvider
  }

  case class SimpleFuncProvider(f: Func, name: Option[String] = None) extends FuncProvider {
    override def fittingFunction(expectedResult: Type)(implicit e: ExecCtx): Option[Func] =
      Some(f).filter(x => if (e.noSubtyping) x.result =:= expectedResult else x.result <:< expectedResult)

    override def wholeType: Type = f.wholeType

    override def idx: Int = f.idx

    override def subIndex: Int = f.subIndex

    override def withIndex(n: Int): FuncProvider = copy(f.withIndex(n))

    override def withName(n: String): FuncProvider = copy(name = Some(n))
  }

  case class GenericFuncProvider(wholeType: Type, symbols: Map[Type, Set[Type]], idx: Int, subIndex: Int, name: Option[String] = None) extends FuncProvider {
    private val genType = typeToFunc(wholeType, idx, subIndex).head

    private val (poly, polyMap) = toPolyType(wholeType)

    val polyBuilder = toFuncBuilder(polyMap.values.toSet, poly)

    def toPolyType(t: Type): (Type, Map[Type, Type]) = {

      val toSymbols = symbols.keySet.map(x => x -> x)
      val toReplace = toSymbols.flatMap(x => symbols(x._1).map(_ -> x._2))
      val repl = t.map(x => toReplace.find(_._1 =:= x).map(_._2).getOrElse(x))

      (repl, toSymbols.toMap)
    }

    def toFuncBuilder(s: Set[Type], t: Type): FuncBuilder = {
      t match {
        case Func1Extractor(a, r@Func1Extractor(_, _)) =>
          ComplexFuncBuilder(toTypeBuilder(s, a), toFuncBuilder(s, r))
        case Func1Extractor(a, r) =>
          SimpleFuncBuilder(toTypeBuilder(s, a), toTypeBuilder(s, r))
      }
    }

    def toTypeBuilder(s: Set[Type], t: Type): TypeBuilder = {
      val found = s.find(_ =:= t)
      found match {
        case Some(value) => Selector(value)
        case None =>
          if (t.typeArgs.nonEmpty)
            Apply(t.typeConstructor, t.typeArgs.map(toTypeBuilder(s, _)))
          else ConstType(t)
      }
    }

    sealed trait FuncBuilder {
      def buildFunc(f: Map[Type, Type]): Func
    }

    case class SimpleFuncBuilder(argBuilder: TypeBuilder, resBuilder: TypeBuilder) extends FuncBuilder {
      override def buildFunc(f: Map[Type, Type]): Func =
        SimpleFunc1(argBuilder.build(f), resBuilder.build(f), idx, subIndex)
    }

    case class ComplexFuncBuilder(argBuilder: TypeBuilder, innerBuilder: FuncBuilder) extends FuncBuilder {
      override def buildFunc(f: Map[Type, Type]): Func =
        ComplexFunc(argBuilder.build(f), innerBuilder.buildFunc(f), idx, subIndex)
    }

    sealed trait TypeBuilder {
      def build(m: Map[Type, Type]): Type
    }

    case class Selector(s: Type) extends TypeBuilder {
      override def build(m: Map[Type, Type]): Type = m(s)
    }

    case class ConstType(t: Type) extends TypeBuilder {
      override def build(m: Map[Type, Type]): Type = t
    }

    case class Apply(tyCon: Type, builders: List[TypeBuilder]) extends TypeBuilder {
      override def build(m: Map[Type, Type]): Type =
        appliedType(tyCon, builders.map(_.build(m)))
    }

    @tailrec
    private def compareSingle(s: Seq[Type], top: Seq[(Type, Type)], cm: Map[Type, Type]): Map[Type, Type] = {
      top match {
        case Seq() => cm
        case (pt, e) +: t =>
          val pta = pt.typeArgs
          val ea = e.typeArgs
          if (pta.nonEmpty && ea.nonEmpty) {
            if (pt.typeConstructor =:= e.typeConstructor) compareSingle(s, pta.zip(ea) ++: t, cm)
            else compareSingle(s, t, cm)
          } else {
            val cn = s.filter(pt <:< _).map(_ -> e)
            val nc = cm ++ cn
            if (nc.size == s.size) nc
            else compareSingle(s, t, nc)
          }
      }
    }


    override def fittingFunction(expectedResult: Type)(implicit e: ExecCtx): Option[Func] = {
      val cand = compareSingle(symbols.keys.toList, Seq((genType.result, expectedResult.dealias)), Map.empty)
      if (cand.size != symbols.size) return None

      val m = cand.map(x => polyMap(x._1) -> x._2)
      val gf = polyBuilder.buildFunc(m)
      //log(s"Generic candidate. cands: $cand exp: $expectedResult, got:  ${gf.result}")
      Some(gf).filter(x => if (e.noSubtyping) x.result =:= expectedResult else x.result <:< expectedResult)
    }

    override def withIndex(n: Int): FuncProvider = copy(idx = n)

    override def withName(n: String): FuncProvider = copy(name = Some(n))
  }

  sealed trait Func extends Indexed[Func] {

    def args: Seq[Type]

    def result: Type

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate

    def wholeTypeTree: Tree = TypeTree(wholeType)

    def wholeType: Type
  }

  case class SimpleFunc1(arg: Type, result: Type, idx: Int, subIndex: Int) extends Func {
    val args: Seq[Type] = Seq(arg)

    override def withIndex(n: Int): SimpleFunc1 = copy(idx = n)

    override val wholeType: Type = arg ==> result

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate =
      trees match {
        case Seq(ar) => ExprCreate.applyExpr(funcTree, ar, TypeTree(arg), TypeTree(result))(ctx.withResult(result))
        case _ => sys.error("Incorrect number of arguments")
      }

  }

  case class ComplexFunc(arg: Type, inner: Func, idx: Int, subIndex: Int) extends Func {
    val args: Seq[Type] = arg +: inner.args

    def result: Type = inner.result

    override def withIndex(n: Int): ComplexFunc = copy(inner = inner.withIndex(n), idx = n)

    override val wholeType: Type = arg ==> inner.wholeType

    def apply(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate =
      trees match {
        case h +: t => inner(ExprCreate.applyExpr(funcTree, h, TypeTree(arg), inner.wholeTypeTree)(ctx.withResult(inner.wholeType)), t)
        case Seq() => sys.error("Incorrect number of arguments. Too small")
      }
  }

  case class ObjectFunc(wholeType: Type, objType: Type, method: MethodSymbol, idx: Int) extends Func {
    val inner = {
      if (method.paramLists.flatten.nonEmpty) {// Currently only single param lists are supported. Just like in Func
        def buildT(args: List[List[Symbol]]): Type = args match {
          case List(s) :: tail => s.info ==> buildT(tail)
          case Nil => method.returnType
        }

        typeToFunc(buildT(method.paramLists), 0, 0).headOption
      } else None
    }

    override def args: Seq[Type] = objType +: inner.map(_.args).getOrElse(Nil)

    override def result: Type = inner.map(_.result).getOrElse(method.returnType)

    override def subIndex: Int = 0

    override def withIndex(n: Int): Func = copy(idx = n)

    override def apply(objTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate = {
      val h = trees.head
      if (inner.nonEmpty) {
        val fTree = q"(x: ${TypeTree(objType)}) => (x.$method):${TypeTree(inner.get.wholeType)}"

        val funcTree = ExprCreate.applyNative(
          h,
          fTree,
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
      case LabeledExtractor(v, t) =>
        typeToFuncProvider(t, idx, subIndex).map(_.withName(v.toString))
      case t@Func1Extractor(_, _) if t.find(_ <:< Types.varType).isDefined =>
        val varSymbols = t.collect.filter(_ <:< Types.varType)
        val basicTypes = varSymbols.filter(x => !(varSymbols - x).exists(y => x <:< y))
        val map = basicTypes.map(x => x -> varSymbols.filter(_ <:< x)).toMap
        List(GenericFuncProvider(t, map, idx, subIndex))
      case t => typeToFunc(t, idx, subIndex).map(SimpleFuncProvider(_))
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
    a match {
      case LabeledExtractor(l, a) =>
        if (a <:< Types.coproductType) CoproductArgs(Types.split2ArgsRec(a, Types.cconsType).map(argsFromA), Some(l))
        else if (a <:< Types.hlistType) ListArgs(Types.split2ArgsRec(a, Types.hconsType).map(argsFromA), Some(a))
        else SingleArg(a, Some(l))
      case a =>
        if (a <:< Types.coproductType) CoproductArgs(Types.split2ArgsRec(a, Types.cconsType).map(argsFromA), None)
        else if (a <:< Types.hlistType) ListArgs(Types.split2ArgsRec(a, Types.hconsType).map(argsFromA), Some(a))
        else SingleArg(a, None)
    }
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

    val wholeTypeWrapper: TypeEqualityWrapper = wholeType
  }

  def toInt[L <: shapeless.Nat : u.WeakTypeTag]: Int = {
    var t = weakTypeOf[L].dealias
    var i = 0
    log(s"toInt $t")
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


  def createContext[L <: shapeless.Nat : u.WeakTypeTag, N <: shapeless.Nat : u.WeakTypeTag,
    C <: HList : u.WeakTypeTag,
    A: u.WeakTypeTag,
    T: u.WeakTypeTag,
    O <: Options : u.WeakTypeTag]: ExecCtx = {
    ExecCtx(
      toInt[N],
      funcsFromCtx(weakTypeOf[C]),
      argsFromA(weakTypeOf[A]),
      weakTypeTag[T].tpe.dealias,
      toInt[L],
      Opts[O]
    )
  }

  case class TypeEqualityWrapper private(t: Type) {
    override def equals(o: Any): Boolean = Timer.timer("TEW equ") {
      o match {
        case o@TypeEqualityWrapper(tt) => (o eq this) || (t eq tt) || (
          size == o.size &&
            t =:= tt
          )
        case _ => false
      }
    }

    val size = Types.size(t)

    override val hashCode: Int = t.typeSymbol.name.decodedName.toString.hashCode | size
  }

  object TypeEqualityWrapper {
    private val cache = mutable.AnyRefMap.empty[Type, TypeEqualityWrapper]
    //Attempt to catch referencial equality.
    //Its easier to check than type equality.
    def apply(t: Type): TypeEqualityWrapper = Timer.timer("TEW cache") {
      Timer.tick("TEW cache req")
      cache.getOrElseUpdate(t, {
        Timer.tick("TEW cache miss")
        new TypeEqualityWrapper(t)
      })
    }
  }

  implicit def wrap(t: Type): TypeEqualityWrapper = TypeEqualityWrapper(t.dealias)

  implicit def unwrap(t: TypeEqualityWrapper): Type = t.t

  case class Opts(
    noLoops: Boolean,
    noSubtyping: Boolean
  )

  object Opts {
    def apply[O <: Options : u.WeakTypeTag]: Opts = Opts(
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

    case class CustomGenCtxTpeProvider private(ctxTypeT: TypeEqualityWrapper, argTypeT: TypeEqualityWrapper, resTypeT: TypeEqualityWrapper) extends GenCtxTpeProvider {

      def ctxType: Type = ctxTypeT

      def argType: Type = argTypeT

      def resType: Type = resTypeT

      def withCtx(ctx: Type): CustomGenCtxTpeProvider = CustomGenCtxTpeProvider(ctx, argTypeT, resTypeT)

      def withArg(arg: Type): CustomGenCtxTpeProvider = CustomGenCtxTpeProvider(ctxTypeT, arg, resTypeT)

      def withRes(res: Type): CustomGenCtxTpeProvider = CustomGenCtxTpeProvider(ctxTypeT, argTypeT, res)

      override val hashCode: Int = super.hashCode()

    }

    object CustomGenCtxTpeProvider {
      type T3 = (TypeEqualityWrapper, TypeEqualityWrapper, TypeEqualityWrapper)
      private val cache = mutable.LongMap.empty[mutable.AnyRefMap[T3, CustomGenCtxTpeProvider]]

      //Again referential equality
      //Size seems to be the best heuristic to catch different types
      def apply(ctx: TypeEqualityWrapper, arg: TypeEqualityWrapper, res: TypeEqualityWrapper): CustomGenCtxTpeProvider = {
        Timer.timer("CGCTP time") {
          Timer.tick("CGCTP count")
          Timer.set("CGCTP size", cache.values.map(_.size).sum)
          val hash = (ctx.size << 20) | (arg.size << 10) | res.size
          cache
            .getOrElseUpdate(hash, mutable.AnyRefMap.empty)
            .getOrElseUpdate((ctx, arg, res), new CustomGenCtxTpeProvider(ctx, arg, res))
        }
      }
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

    override def resType: Type = result

    lazy val provider: GenCtxTpeProvider.CustomGenCtxTpeProvider =
      GenCtxTpeProvider.CustomGenCtxTpeProvider(ctx.wholeTypeWrapper, args.wholeTypeWrapper, resultT)
  }

  import bshapeless.exprs.{Expr => MExpr}

  class ExprTreeBuilder(eval: u.Tree => Any) extends ExprBuilderGeneric[StructureTree, MExpr[Nothing, Nothing, Nothing], ({type I[_] = Tree})#I] {
    import bshapeless.exprs

    implicit def asNothing(e: MExpr[_, _, _]): MExpr[Nothing, Nothing, Nothing] =
      e.asInstanceOf

    override def buildHNil: MExpr[Nothing, Nothing, Nothing] =
      exprs.HNilCreate[Nothing, Nothing]

    override def buildHList(h: StructureTree, t: StructureTree): MExpr[Nothing, Nothing, Nothing] = {
      exprs.HListResultSplit[Nothing, Nothing, Nothing, Nothing](build(h), build(t))
    }

    override def buildCNil: MExpr[Nothing, Nothing, Nothing] =
      exprs.CNilCreate[Nothing, Nothing]

    override def buildCoproduct(h: StructureTree, t: StructureTree): MExpr[Nothing, Nothing, Nothing] =
      exprs.CoproductArgSplit[Nothing, Nothing, Nothing, Nothing](build(h), build(t))

    override def buildSelectArg(n: Int): MExpr[Nothing, Nothing, Nothing] =
      exprs.FromArgsSelect(n)

    override def buildFromArg: MExpr[Nothing, Nothing, Nothing] =
      exprs.FromArgsEq[Nothing, Nothing, Nothing](implicitly[Nothing <:< Nothing])

    override def buildSelectCtx(n: Int): MExpr[Nothing, Nothing, Nothing] =
      exprs.FromCtxSelect(n)

    override def buildApply(f: StructureTree, a: StructureTree): MExpr[Nothing, Nothing, Nothing] =
      exprs.Apply[Nothing, Nothing, Nothing, Nothing](build(f), build(a))

    override def buildApplyNative(name: String, func: u.Tree, memberFunc: Boolean, arg: StructureTree): MExpr[Nothing, Nothing, Nothing] = {
      val f: Nothing => Nothing = eval(func).asInstanceOf[Nothing => Nothing]
      exprs.ApplyNative[Nothing, Nothing, Nothing, Nothing](build(arg))(f, name, memberFunc)
    }

    override def buildPair(f: StructureTree, s: StructureTree): MExpr[Nothing, Nothing, Nothing] = {
      exprs.PairExp[Nothing, Nothing, Nothing, Nothing](build(f), build(s))
    }

    override def buildAbstractVal(b: StructureTree): MExpr[Nothing, Nothing, Nothing] = {
      if(b.typ.asInstanceOf[ExprType.AbstractVal].argIsHList)
        exprs.AbstractVal[Nothing, Nothing, Nothing, Nothing](build(b).asInstanceOf)
      else
        exprs.AbstractValNotH[Nothing, Nothing, Nothing, Nothing](build(b).asInstanceOf)
    }

    override def buildAbstractFun(b: StructureTree): MExpr[Nothing, Nothing, Nothing] =
      exprs.AbstractFunc[Nothing,Nothing,Nothing,Nothing](build(b).asInstanceOf)

    override def buildInlResult(a: StructureTree): MExpr[Nothing, Nothing, Nothing] =
      exprs.InlResultExpr[Nothing,Nothing,Nothing, Nothing](build(a))

    override def buildInrResult(a: StructureTree): MExpr[Nothing, Nothing, Nothing] =
      exprs.InrResultExpr[Nothing,Nothing,Nothing,Nothing](build(a))
  }
}
