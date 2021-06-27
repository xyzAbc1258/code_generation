package bshapeless

import bshapeless.exprs.ExprBuilderGeneric
import bshapeless.exprs.ExprTree
import bshapeless.exprs.ExprType
import bshapeless.utils.AllEqualWrapper
import shapeless.HList

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec
import scala.collection.mutable
import scala.language.implicitConversions
import scala.util.Random

trait GeneratorTypes extends FunctionProviders {

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

    case class AbstractVal(inner: StructureTree, argIsHList: Boolean, argTpt: AllEqualWrapper[Type]) extends StructureTree("abstractVal", ExprType.AbstractVal(argIsHList)) {
      override def build[R](b: Builder[R]): R = b.buildAbstractVal(inner, argIsHList, TypeTree(argTpt.t))
    }

    case class AbstractFun(inner: StructureTree, argTpt: AllEqualWrapper[Type]) extends StructureTree("abstractFun", ExprType.AbstractFun) {
      override def build[R](b: Builder[R]): R = b.buildAbstractFun(inner, TypeTree(argTpt.t))
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
      Candidate(
        q"$ns.HNilCreate.apply[$ctxTypeT, $argTypeT]",
        StructureTree.HNilTree(ctx.argType.typeSymbol.name.decodedName.toString)
      )(ctx.withResult(Types.hnilType))

    def hList(head: Candidate, tail: Candidate, hType: Tree, tType: Tree)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.HListResultSplit[$ctxTypeT, $argTypeT, $hType, $tType]($head, $tail)",
        StructureTree.HListResult(head, tail),
        head, tail
      )

    def cnil(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.CNilCreate.apply[$ctxTypeT, $resTypeT]",
        StructureTree.CNilArg(resType.typeSymbol.name.decodedName.toString)
      )(ctx.provider.withArg(Types.cnilType))

    def coproduct(h: Candidate, t: Candidate, hType: Type, tType: Type)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.CoproductArgSplit[$ctxTypeT, ${ttr(hType)}, ${ttr(tType)}, $resTypeT]($h, $t)",
        StructureTree.CoproductArgs(h, t),
        h, t
      )(ctx.provider.withArg(hType +:+: tType))

    def fromArgsSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.FromArgsSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})",
        StructureTree.SelectArgs(n)
      )

    def fromArgsEq(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.FromArgsEq.create[$ctxTypeT, $argTypeT, $resTypeT]",
        StructureTree.FromArgsEq(resType.typeSymbol.name.decodedName.toString)
      )

    def fromCtxSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.FromCtxSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})",
        StructureTree.SelectCtx(n)
      )

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
        q"$ns.PairExp[$ctxTypeT, $argTypeT, ${ttr(resType.firstTypeArg)}, ${ttr(resType.secondTypeArg)}]($a, $b)",
        StructureTree.Pair(a, b),
        a, b
      )

    def abstractVal(e: Candidate)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.AbstractVal[$ctxTypeT, $argTypeT, ${ttr(resType.firstTypeArg)}, ${ttr(resType.secondTypeArg)}]($e)",
        StructureTree.AbstractVal(e, true, AllEqualWrapper(resType.firstTypeArg)),
        e
      )


    def abstractValNotH(e: Candidate)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.AbstractValNotH[$ctxTypeT, $argTypeT, ${ttr(resType.firstTypeArg)}, ${ttr(resType.secondTypeArg)}]($e)",
        StructureTree.AbstractVal(e, false, AllEqualWrapper(resType.firstTypeArg)),
        e
      )

    def abstractFunc(e: Candidate)(implicit ctx: ExecCtx): Candidate =
      Candidate(
        q"$ns.AbstractFunc[$ctxTypeT, $argTypeT, ${ttr(resType.firstTypeArg)}, ${ttr(resType.secondTypeArg)}]($e)",
        StructureTree.AbstractFun(e, AllEqualWrapper(resType.firstTypeArg)),
        e
      )

    def withMapCtx(f: Tree, e: Tree)(implicit ctx: ExecCtx): Tree =
      q"$ns.WithMapCtx($f, $e)"

    def inlResult(e: Candidate)(implicit ctx: ExecCtx): Candidate = {
      Candidate(
        q"$ns.InlResultExpr[$ctxTypeT, $argTypeT, ${ttr(resType.firstTypeArg)}, ${ttr(resType.secondTypeArg)}]($e)",
        StructureTree.InlResult(e),
        e
      )
    }

    def inrResult(e: Candidate)(implicit ctx: ExecCtx): Candidate = {
      Candidate(
        q"$ns.InrResultExpr[$ctxTypeT, $argTypeT, ${ttr(resType.firstTypeArg)}, ${ttr(resType.secondTypeArg)}]($e)",
        StructureTree.InrResult(e),
        e
      )
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
      if (nn.forall(_.isDefined)) {
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

  @tailrec
  final def applyFunc(f: Func)(funcTree: Candidate, trees: Seq[Candidate])(implicit ctx: ExecCtx): Candidate = {
    (f, trees) match {
      case (s: SimpleFunc1, Seq(arg)) =>
        ExprCreate.applyExpr(funcTree, arg, TypeTree(s.arg), TypeTree(s.result))(ctx.withResult(s.result))
      case (s: ComplexFunc, hArg +: tailArgs) =>
        val partialApp = ExprCreate.applyExpr(
          funcTree, hArg, TypeTree(s.arg), s.inner.wholeTypeTree
        )(ctx.withResult(s.inner.wholeType))
        applyFunc(s.inner)(partialApp, tailArgs)
      case (s: ObjectFunc, objectTree +: tailArgs) => //funcTree isnt necessary here since its ObjectFuncProvider only, not any real value
        val funcTree = ExprCreate.applyNative(
          objectTree,
          fun = q"(x: ${TypeTree(s.objType)}) => (x.${s.method}):${TypeTree(s.resultFuncType)}",
          name = s.method.name.decodedName.toString,
          member = true
        )(ctx.withResult(s.resultFuncType))
        s.inner match {
          case Some(inner) => applyFunc(inner)(funcTree, tailArgs)
          case None => funcTree.ensuring(tailArgs.isEmpty)
        }
    }
  }


  def typeToFuncProvider(t: Type, idx: Int, subIndex: Int = 0): Seq[FuncProvider] = {
    t.dealias match {
      case LabeledExtractor(v, t) =>
        typeToFuncProvider(t, idx, subIndex).map(_.withName(v.toString))
      case t@Func1Extractor(_, _) if t.find(_ <:< Types.varType).isDefined =>
        val varSymbols = t.collect.filter(_ <:< Types.varType)
        val basicTypes = varSymbols.filter(x => !(varSymbols - x).exists(y => x <:< y))
        val map = basicTypes.map(x => x -> varSymbols.filter(_ <:< x)).toMap
        Seq(GenericFuncProvider(t, map, idx, subIndex))
      case t if t <:< Types.objectProviderTpe =>
        val tpe = t.firstTypeArg
        val methods = userMethods(tpe)
        methods.flatMap(x =>
          if (x.typeParams.nonEmpty) GenericFuncProvider(ObjectPolyFunc(t, tpe, x, idx, subIndex), None)::Nil
          else ObjectFunc(t, tpe, x, idx).map(SimpleFuncProvider(_))
        )
      case t => typeToFunc(t, idx, subIndex).map(SimpleFuncProvider(_))
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

  case class ContextFunctions(providers: Array[FuncProvider], wholeTypeOpt: Option[Type]) {
    @inline
    private def intersect(t: Seq[Type]): Type = {
      t match {
        case Seq(t) => t
        case l if l.head.isInstanceOf[ObjectFunc] => l.head.asInstanceOf[ObjectFunc].wholeType
        case l => internal.intersectionType(l.toList)
      }
    }

    def prepend(newProvider: Seq[FuncProvider]): ContextFunctions = {
      ContextFunctions(
        newProvider ++: providers.map(_.incIdx()),
        wholeTypeOpt.map(intersect(newProvider.map(_.wholeType)) :::: _)
      )
    }

    def wholeType: Type = wholeTypeOpt getOrElse {
      providers.groupBy(_.idx).map[(Int, Type)] { case (i, f) => i -> intersect(f.map(_.wholeType))
      }.toList.sortBy(_._1).map(_._2).foldRight(Types.hnilType) {
        _ :::: _
      }
    }

    val wholeTypeWrapper: TypeEqualityWrapper = wholeType
  }

  def toInt[L <: shapeless.Nat : u.WeakTypeTag]: Int = {
    var t = weakTypeOf[L].dealias
    var i = 0
    log(s"toInt $t")
    while (t <:< Types.succType) {
      t = t.firstTypeArg.dealias
      i += 1
    }
    i
  }

  def funcsFromCtx(t: Type): ContextFunctions = {
    val types = Types.split2ArgsRec(t, Types.hconsType)
    ContextFunctions(types.zipWithIndex.flatMap((typeToFuncProvider(_: Type, _: Int)).tupled).toArray, Some(t))
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
        case o@TypeEqualityWrapper(tt) => (o eq this) || (t eq tt) || (size == o.size && t =:= tt)
        case _ => false
      }
    }

    val size: Int = Types.size(t)

    override val hashCode: Int = Types.hash(t) * 41 + size
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

    implicit def wrap(t: Type): TypeEqualityWrapper = apply(t.dealias)
  }

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
      private val cache = mutable.AnyRefMap.empty[T3, CustomGenCtxTpeProvider]

      //Again referential equality
      //Size seems to be the best heuristic to catch different types
      def apply(ctx: TypeEqualityWrapper, arg: TypeEqualityWrapper, res: TypeEqualityWrapper): CustomGenCtxTpeProvider = {
        Timer.timer("CGCTP time") {
          Timer.tick("CGCTP count")
          Timer.set("CGCTP size", cache.size)
          cache.getOrElseUpdate((ctx, arg, res), new CustomGenCtxTpeProvider(ctx, arg, res))
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
    depth: Int,
    ctx: ContextFunctions,
    args: Args,
    resultT: TypeEqualityWrapper,
    limit: Int,
    options: Opts
  ) extends GenCtxTpeProvider {

    def result: Type = resultT.t

    def zeroed: ExecCtx = copy(depth = 0)

    def decreaseDepthWithResult(newResult: Type): ExecCtx = {
      if (depth > 0) copy(depth = depth - 1, resultT = newResult.dealias.map(_.dealias))
      else sys.error(s"Cannot decrease $depth")
    }

    def withDepth(t: Int): ExecCtx = copy(depth = t)

    def withCtx(f: ContextFunctions => ContextFunctions): ExecCtx = copy(ctx = f(ctx))

    def withArgs(t: Args): ExecCtx = copy(args = t)

    def withResult(t: Type): ExecCtx = copy(resultT = t.dealias)

    override lazy val hashCode: Int = super.hashCode()

    def ctxType: Type = ctx.wholeType

    def argType: Type = args.wholeType

    @inline val noLoops: Boolean = options.noLoops
    @inline val noSubtyping: Boolean = options.noSubtyping

    override def resType: Type = result

    lazy val provider: GenCtxTpeProvider.CustomGenCtxTpeProvider =
      GenCtxTpeProvider.CustomGenCtxTpeProvider(ctx.wholeTypeWrapper, args.wholeTypeWrapper, resultT)
  }

  class ExprTreeBuilder(eval: u.Tree => Any) extends bshapeless.exprs.ExprTreeBuilder[({type W[_] = Tree})#W](eval)


  case class ExprRawTreeBuilder(
    ctxList: Seq[Tree], arg: Any
  ) extends ExprBuilderGeneric[StructureTree, Tree, ({type T[_] = Tree})#T] {

    override def buildHNil: Tree = q"shapeless.HNil"

    override def buildHList(h: StructureTree, t: StructureTree): Tree =
      q"shapeless.::(${build(h)}, ${build(t)})"

    override def buildCNil: Tree = q"${untyped(arg.asInstanceOf[Tree])}.impossible"

    override def buildCoproduct(h: StructureTree, t: StructureTree): Tree = {
      def withNewArg(nArg: Tree)(st: StructureTree): Tree = ExprRawTreeBuilder(ctxList, nArg).build(st)
      def getVar(tpe: Type) = Typed(Ident(TermName(s"a_${Random.nextInt(899) + 100}")), TypeTree(tpe))

      val argType = Option(arg.asInstanceOf[Tree].tpe).getOrElse(arg.asInstanceOf[Typed].tpt.asInstanceOf[TypeTree].tpe.secondTypeArg)

      val inlType = argType.dealias.firstTypeArg
      val inrType = argType.dealias.secondTypeArg

      val matchL = {
        val inlVar = getVar(appliedType(weakTypeOf[shapeless.Inl[_, _]].typeConstructor, inlType, inrType))
        val pat = Apply(q"shapeless.Inl", List(Bind(inlVar.expr.asInstanceOf[Ident].name, Typed(Ident(termNames.WILDCARD), TypeTree(inlType)))))
        cq"$pat => ${withNewArg(untyped(inlVar))(h)}"
      }

      val matchR = {
        val inrVar = getVar(appliedType(weakTypeOf[shapeless.Inr[_, _]].typeConstructor, inlType, inrType))
        val pat = Apply(q"shapeless.Inr", List(Bind(inrVar.expr.asInstanceOf[Ident].name, Typed(Ident(termNames.WILDCARD), TypeTree(inrType)))))
        cq"$pat => ${withNewArg(inrVar)(t)}"
      }

      q"""${untyped(arg.asInstanceOf[Tree])} match { case ..${List(matchL, matchR)} }"""
    }

    private def untyped(e: Tree): Tree = e match {
      case Apply(t, args) => Apply(untyped(t), args.map(untyped))
      case Select(t, n) => Select(untyped(t), n)
      case ValDef(_, n, _, _) => Ident(n)
      case Typed(e, _) => e
      case e => e
    }


    override def buildSelectArg(n: Int): Tree = untyped(arg.asInstanceOf[Seq[Tree]](n))

    override def buildFromArg: Tree = untyped(arg.asInstanceOf[Tree])

    override def buildSelectCtx(n: Int): Tree = untyped(ctxList(n))

    def buildFuncApp(funcTree: Tree, argTree: Tree): Tree = q"$funcTree($argTree)"

    override def buildApply(f: StructureTree, a: StructureTree): Tree =
      buildFuncApp(build(f), build(a))

    override def buildApplyNative(name: String, func: Tree, memberFunc: Boolean, arg: StructureTree): Tree = {
      buildFuncApp(func, build(arg))
    }

    override def buildPair(f: StructureTree, s: StructureTree): Tree = q"(${build(f)}, ${build(s)})"

    private def buildValDef(name: String, tpt: Tree): Tree = {
      ValDef(Modifiers(Flag.PARAM), TermName(name), tpt, EmptyTree)
    }

    private def buildAbstract(newCtx: Seq[Tree], newArgs: Any)(ident: Tree, b: StructureTree): Tree = {
      val newBuilder = ExprRawTreeBuilder(newCtx, newArgs)
      val bodyTree = newBuilder.build(b)
      q"($ident) => $bodyTree"
    }

    override def buildAbstractVal(b: StructureTree, argsIsHList: Boolean, argType: Tree): Tree = {
      if (argsIsHList) {
        val args = arg.asInstanceOf[Seq[Tree]]
        val newVar = buildValDef(s"a_${args.size}", argType)
        buildAbstract(ctxList, newVar +: args)(newVar, b)
      } else {
        val newVar = buildValDef("a_0", argType)
        buildAbstract(ctxList, Seq(newVar, arg))(newVar, b)
      }
    }

    override def buildAbstractFun(b: StructureTree, argType: Tree): Tree = {
      val stringName = s"u_${ctxList.size}"
      val newVar: Tree = buildValDef(stringName, argType)
      buildAbstract(newVar +: ctxList, arg)(newVar, b)
    }

    override def buildInlResult(a: StructureTree): Tree = q"shapeless.Inl(${build(a)})"

    override def buildInrResult(a: StructureTree): Tree = q"shapeless.Inr(${build(a)})"
  }


}
