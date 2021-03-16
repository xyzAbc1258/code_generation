package bshapeless

import bshapeless.exprs.ExprStringBuilder
import bshapeless.exprs.{Expr => MExpr}
import shapeless._

import scala.collection.mutable
import scala.language.experimental.macros
import scala.reflect.api.Universe
import scala.reflect.macros.blackbox
import scala.tools.reflect.ToolBox
import scala.tools.reflect.mkConsoleFrontEnd

trait Options

trait NoLoops extends Options

trait NoSubtyping extends Options

case class MGenerator[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options](expressions: Seq[MExpr[C, A, T]])

object MGenerator {

  def apply[N <: Nat, C <: HList, A, T](implicit e: MGenerator[Nat._5, N, C, A, T, Options]): MGenerator[Nat._5, N, C, A, T, Options] = e

  def applyO[N <: Nat, C <: HList, A, T, O <: Options](implicit e: MGenerator[Nat._5, N, C, A, T, O]): MGenerator[Nat._5, N, C, A, T, O] = e

  def applyL[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options](implicit e: MGenerator[L, N, C, A, T, O]): MGenerator[L, N, C, A, T, O] = e

  implicit def fromMacro[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options]: MGenerator[L, N, C, A, T, O] = macro MacroImpl.macroImpl[L, N, C, A, T, O]

  def generateStrings[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options]: Seq[String] = macro MacroImpl.macroImplString[L, N, C, A, T, O]

  class MacroImpl(val c: blackbox.Context) extends MacroSimplImpl {
    override type U = c.universe.type
    override val u = c.universe

    import u._

    def macroImpl[L <: Nat : c.WeakTypeTag, N <: Nat : c.WeakTypeTag, C <: HList : c.WeakTypeTag, A: c.WeakTypeTag, T: c.WeakTypeTag, O <: Options : c.WeakTypeTag]: c.Tree =
      buildResult[u.Tree, L, N, C, A, T, O] { case (smallestCandidates, _) =>
        val reified = {
          val deps = smallestCandidates.flatMap(_.allDepesWithItself).distinct.sortBy(_.no)
          val intermediateValueDefs = deps.map {
            _.valDef
          }
          log(s"Deps: " + deps.map(_.no).mkString("\n"))
          val ss = q"Seq(..${smallestCandidates.map(_.term)})"
          val reified =
            q"""
                new MGenerator[
                    ${TypeTree(weakTypeOf[L])},
                    ${TypeTree(weakTypeOf[N])},
                    ${TypeTree(weakTypeOf[C])},
                    ${TypeTree(weakTypeOf[A])},
                    ${TypeTree(weakTypeOf[T])},
                    ${TypeTree(weakTypeOf[O])}]($ss)
                """
          q"""{
                  ..$intermediateValueDefs
                  $reified
               }"""
        }
        log(Timer.printable)
        reified
      }

    def macroImplString[L <: Nat : c.WeakTypeTag, N <: Nat : c.WeakTypeTag, C <: HList : c.WeakTypeTag, A: c.WeakTypeTag, T: c.WeakTypeTag, O <: Options : c.WeakTypeTag]: c.Tree = {
      val strings = macroImplBaseStringU[L, N, C, A, T, O].map(Constant(_)).map(Literal(_))
      q"Seq(..$strings)"
    }
  }

  object RuntimeMacroImpl extends MacroSimplImpl {
    override type U = scala.reflect.runtime.universe.type
    val u = scala.reflect.runtime.universe
    override val c: blackbox.Context = null // not very nice solution...

    val tb = scala.tools.reflect.ToolBox(u.rootMirror).mkToolBox(mkConsoleFrontEnd())

    override def log(msg: String, force: Boolean): Unit = println(s"[Macro log] $msg")

    def generate[
      L <: Nat : u.WeakTypeTag,
      N <: Nat : u.WeakTypeTag,
      C <: HList : u.WeakTypeTag,
      A: u.WeakTypeTag,
      T: u.WeakTypeTag,
      O <: Options : u.WeakTypeTag
    ]: MGenerator[L, N, C, A, T, O] = buildResult[MGenerator[L, N, C, A, T, O], L, N, C, A, T, O] { case (candidates, _) =>
      val builder = new ExprTreeBuilder(tb.eval)
      val mapped = candidates.map(_.structure).map(builder.build).map(_.asInstanceOf[MExpr[C, A, T]])
      new MGenerator[L, N, C, A, T, O](mapped)
    }

    def generateStrings[
      L <: Nat : u.TypeTag,
      N <: Nat : u.TypeTag,
      C <: HList : u.TypeTag,
      A: u.TypeTag,
      T: u.TypeTag,
      O <: Options : u.TypeTag
    ]: Seq[String] = {
      macroImplBaseStringU[L, N, C, A, T, O]
    }
  }

  trait MacroSimplImpl extends GeneratorTypes {

    import u._

    object Stage extends Enumeration {
      val FromArgs, FromCtx, FuncApply, PairGen, Normal, FuncGen, GenComposite, FromCopro = Value
    }

    object Cache {

      private val cutBranches: mutable.AnyRefMap[(GenCtxTpeProvider, Stage.Value), Int] = mutable.AnyRefMap.empty

      private val m: mutable.AnyRefMap[GenCtxTpeProvider, Set[Candidate]] = mutable.AnyRefMap.empty

      private val stackHashCodeMap: mutable.LongMap[Seq[ExecCtx]] = mutable.LongMap.empty

      def cached(stage: Stage.Value)(f: => Set[Candidate])(implicit e: ExecCtx): Set[Candidate] = {
        Timer.tick("cached - entry")

        val tpeProvider = e.provider
        val shouldCut = Timer.timer("Cut detection") {
          cutBranches.get(tpeProvider, stage).exists(_ >= e.depth)
        }
        if (shouldCut) {
          Timer.tick("Cut!")
          return Set()
        }
        val breakLoops = Timer.timer("loop detection") {
          e.noLoops && stackHashCodeMap
            .getOrElse(tpeProvider.hashCode, Nil)
            .exists(x => (x.provider eq tpeProvider) && !(x eq e))
        }
        val existing: Set[Candidate] = Timer.timer("cache check") {
          m.getOrElse(tpeProvider, {
            Timer.tick("cache miss")
            Set.empty[Candidate]
          })
        }
        if (breakLoops) {
          Timer.tick("Break")
          return existing
        }
        if (existing.size >= e.limit) {
          Timer.tick("Used calculated")
          return existing
        }
        val hash = tpeProvider.hashCode
        stackHashCodeMap.updateWith(hash)(_ map (e +: _) orElse Some(Seq(e)))
        val next = f
        stackHashCodeMap.updateWith(hash)(_ map (_.tail) filter (_.nonEmpty))
        if (next.isEmpty)
          cutBranches.updateWith(tpeProvider, stage)(_ map (_ max e.depth) orElse Some(e.depth))
        val newAll = Utils.concat(existing, next)
        m.update(tpeProvider, newAll)
        newAll
      }
    }


    implicit class Extensions(o: Set[Candidate]) {
      def limit(implicit e: ExecCtx): Set[Candidate] = {
        if (o.size <= e.limit) o
        else o.toSeq.sortBy(_.size).take(e.limit).toSet
      }
    }

    object Utils {

      @inline def concatLazy(opt1: => Set[Candidate], opt2: => Set[Candidate], opt3: => Set[Candidate])(implicit c: ExecCtx): Set[Candidate] = {
        val current1 = opt1
        if (current1.size >= c.limit) return current1.limit
        val current2 = current1 ++ opt2
        if (current2.size >= c.limit) return current2.limit
        (current2 ++ opt3).limit
      }

      @inline def concat(opts: Set[Candidate]*)(implicit c: ExecCtx): Set[Candidate] = opts.toSet.flatten.limit

      def product[A](s: Seq[Set[A]]): Set[Seq[A]] = {
        s match { //Most common cases are resolved without recursion
          case Seq() => Set(Nil)
          case Seq(h) => h.map(Seq(_))
          case Seq(h, t) => for (sh <- h; st <- t) yield Seq(sh, st)
          case Seq(h, t, r) => for (sh <- h; st <- t; sr <- r) yield Seq(sh, st, sr)
          case h +: t => for (sh <- h; st <- product(t)) yield sh +: st
        }
      }

    }


    def generateFromCtxFunctions(implicit ctx: ExecCtx): Set[Candidate] = {
      if (ctx.depth == 0) Set.empty
      else Cache.cached(Stage.FuncApply) {
        val candidates = Timer.timer("Choose correct functions") {
          ctx.ctx.providers.flatMap(_.fittingFunction(ctx.result, !ctx.noSubtyping)).toSet
        }
        var count = 0
        val fff = for (c <- candidates) yield {
          if (count >= ctx.limit) {
            Set.empty
          } else {
            val argsTrees = c.args.map(ctx.decreaseDepthWithResult)
              .foldLeft[Seq[Set[Candidate]]](Seq.empty) { //Generate till first failure
                case (l, t) if l.headOption.exists(_.isEmpty) => l
                case (l, t) => generateFunc(t) +: l
              }.reverse

            if (argsTrees.headOption.exists(_.isEmpty)) Set.empty
            else {
              val argumentLists = Utils.product(argsTrees)
              val funcExpr = ExprCreate.fromCtxSelect(c.idx)(ctx.withResult(c.wholeType))
              val s = argumentLists.map(argumentList => applyFunc(c)(funcExpr, argumentList))
              count += s.size
              s
            }
          }
        }
        fff.flatten.limit
      }
    }

    def generateFromArgs(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached(Stage.FromArgs) {
      ctx.args match { //Can we take result from arguments
        case SingleArg(t, _) if t <:< ctx.result => Set(ExprCreate.fromArgsEq)
        case a: ListArgs => Timer.timer("m_<:<") {
          a.subTypeIndices(ctx.result).map(ExprCreate.fromArgsSelect).toSet
        }
        case CoproductArgs(_, _) => sys.error("Shouldn't be here")
        case _ => Set.empty
      }
    }

    def generatePair(implicit ctx: ExecCtx): Set[Candidate] = {
      if (ctx.result <:< Types.pairType) Cache.cached(Stage.PairGen) { //Is result a pair ?
        val e1 = generateNormal(ctx.withResult(ctx.result.firstTypeArg))
        if (e1.isEmpty) return Set.empty
        val e2 = generateNormal(ctx.withResult(ctx.result.secondTypeArg))
        (for (e1t <- e1; e2t <- e2) yield ExprCreate.pair(e1t, e2t)).limit
      } else Set.empty
    }

    def generateNormal(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached(Stage.Normal) {
      lazy val simpleCases = generateFromArgs
      lazy val fromFuncs = generateFromCtxFunctions //Can we generate result from functions from context
      lazy val pairs = generatePair
      Utils.concatLazy(simpleCases, fromFuncs, pairs)
    }

    def generateFunc(implicit ctx: ExecCtx): Set[Candidate] = {
      ctx.result match {
        case Func1Extractor(t, r) => //Result is a function
          Cache.cached(Stage.FuncGen) {
            t match {
              case t@Func1Extractor(_, _) => //Result argument is a function
                generateFunc(
                  ctx.withCtx(c => c.prepend(typeToFuncProvider(t, 0))).withResult(r)
                ).map(ExprCreate.abstractFunc).limit
              case t => //Result argument is not a function
                ctx.args match {
                  case e: SingleArg =>
                    generateFunc {
                      ctx.withArgs(ListArgs(argsFromA(t) :: e :: Nil)).withResult(r)
                    }.map(ExprCreate.abstractValNotH).limit
                  case la: ListArgs =>
                    generateFunc {
                      ctx.withArgs(la.prepend(argsFromA(t))).withResult(r)
                    }.map(ExprCreate.abstractVal).limit
                  case CoproductArgs(_, _) => sys.error("Coproduct shouldnt be here")
                }
            }
          }
        case _ => generateNormal(ctx) //Result is not a function
      }
    }

    def generateCompositeHList(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached(Stage.GenComposite) {
      val sTypes = Types.split2ArgsRec(ctx.result, Types.hconsType)
      val options = sTypes.map(ctx.withResult).map(generateComposite(_))
      if (options.exists(_.isEmpty)) Set.empty
      else {
        options.zip(sTypes).foldRight((Set(ExprCreate.hnil), Types.hnilType)) {
          case ((e, et), (r, rt)) =>
            (for (e1 <- e; r1 <- r) yield
              ExprCreate.hList(e1, r1, TypeTree(et), TypeTree(rt))(ctx.withResult(et :::: rt))
              ).toSeq.sortBy(_.size).take(ctx.limit).toSet -> (et :::: rt)
        }._1
      }
    }

    def generateCompositeCoproduct(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached(Stage.GenComposite) {
      val a1 = ctx.result.firstTypeArg
      val rest = ctx.result.secondTypeArg
      val a1Trees = generateComposite(ctx.withResult(a1))
      val restTrees = if (rest <:< Types.cnilType) Set.empty else generateComposite(ctx.withResult(rest))
      val a1TreesInl = a1Trees.map(ExprCreate.inlResult(_))
      val restTreesInr = restTrees.map(ExprCreate.inrResult(_))
      Utils.concat(a1TreesInl, restTreesInr)
    }

    def generateComposite(implicit ctx: ExecCtx): Set[Candidate] = {
      if (ctx.result <:< Types.hlistType) generateCompositeHList
      else if (ctx.result <:< Types.cconsType) generateCompositeCoproduct
      else generateFunc
    }

    def generateFromCoproduct(implicit ctx: ExecCtx): Set[Candidate] = {
      ctx.args match {
        case CoproductArgs(t, _) => Cache.cached(Stage.FromCopro) {
          val mapped = t.map(ctx.withArgs).map(generateComposite(_))
          if (mapped.exists(_.isEmpty)) {
            val tt = t.zip(mapped).filter(_._2.isEmpty).map(_._1)
            log(s"No implicit for $ctx Not defined for $tt")
            Set.empty
          } else {
            val trees = mapped.zip(t.map(_.wholeType))
            trees.foldRight((Set(ExprCreate.cnil), Types.cnilType)) { case ((e, t), (f, ft)) =>
              (for (e1 <- e; f1 <- f) yield ExprCreate.coproduct(e1, f1, t, ft)) -> (t +:+: ft)
            }._1
          }
        }
        case _ => generateComposite(ctx)
      }
    }

    protected def buildResult[R,
      L <: Nat : u.WeakTypeTag,
      N <: Nat : u.WeakTypeTag,
      C <: HList : u.WeakTypeTag,
      A: u.WeakTypeTag,
      T: u.WeakTypeTag,
      O <: Options : u.WeakTypeTag](
      f: (Seq[Candidate], ExecCtx) => R
    ): R = {
      val ctx = createContext[L, N, C, A, T, O]
      val exprs = Timer.timer("Generation")(generateFromCoproduct(ctx))

      exprs match {
        case x if x.isEmpty =>
          log(Timer.printable)
          sys.error(s"Implicit not found for $ctx")
        case value =>
          val smallestCandidates = value.toSeq.sortBy(_.size).take(ctx.limit)
          log(s"Candidates count: ${value.size}")

          f(smallestCandidates, ctx)
      }
    }

    protected def macroImplBaseStringU[
      L <: Nat : u.WeakTypeTag,
      N <: Nat : u.WeakTypeTag,
      C <: HList : u.WeakTypeTag,
      A: u.WeakTypeTag,
      T: u.WeakTypeTag,
      O <: Options : u.WeakTypeTag
    ]: Seq[String] = buildResult[Seq[String], L, N, C, A, T, O] { case (values, ctx) =>
      log(Timer.printable)
      val hv = ctx.ctx.providers.map(x => x.name -> x.idx)
        .distinct.sortBy(_._2).map(x => x._1.getOrElse(s"func_${x._2}"))
        .foldRight[HList](HNil)(_ :: _)
      val av = ctx.args.name.getOrElse {
        ctx.args match {
          case SingleArg(_, _) => "arg"
          case ListArgs(t, _) =>
            t.zipWithIndex.map(x => x._1.name.getOrElse(s"arg${x._2}")).foldRight[HList](HNil)(_ :: _)
          case CoproductArgs(_, _) => "arg"
        }
      }
      val stringBuilder = new ExprStringBuilder[({type I[_] = Tree})#I]
      val strings = values.map(_.structure)
        .map(stringBuilder.build)
        .map(_.build(hv, av))

      strings
    }
  }

}
