package bshapeless

import bshapeless.exprs.{Expr => MExpr}
import shapeless._

import scala.annotation.tailrec
import scala.collection.immutable.AbstractSeq
import scala.collection.immutable.LinearSeq
import scala.collection.mutable
import scala.reflect.macros.blackbox
import scala.language.experimental.macros

trait Options

trait NoLoops extends Options

case class MGenerator[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options](expressions: Seq[MExpr[C, A, T]])

object MGenerator {

  def apply[N <: Nat, C <: HList, A, T](implicit e: MGenerator[Nat._5, N, C, A, T, Options]): MGenerator[Nat._5, N, C, A, T, Options] = e

  def applyO[N <: Nat, C <: HList, A, T, O <: Options](implicit e: MGenerator[Nat._5, N, C, A, T, O]): MGenerator[Nat._5, N, C, A, T, O] = e

  def applyL[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options](implicit e: MGenerator[L, N, C, A, T, O]): MGenerator[L, N, C, A, T, O] = e

  implicit def fromMacro[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options]: MGenerator[L, N, C, A, T, O] = macro MacroImpl.macroImpl[L, N, C, A, T, O]


  class MacroImpl(val c: blackbox.Context) extends CommonTypes {

    import c.universe._

    object Cache {

      private val m: mutable.Map[ExecCtx, Seq[Candidate]] = mutable.Map.empty

      private val stack: mutable.Stack[ExecCtx] = mutable.Stack.empty

      @inline def inStack[T](f: => Seq[Candidate])(implicit e: ExecCtx): Seq[Candidate] = {
        stack.push(e)
        val v = f
        stack.pop()
        v
      }

      def cached(f: => Seq[Candidate])(implicit e: ExecCtx): Seq[Candidate] = {
        val breakLoops = e.noLoops && stack.exists(x => x.zeroed == e.zeroed && !(x eq e))
        val existing = m.getOrElse(e.zeroed, Nil)
        if (existing.nonEmpty) {
          if (breakLoops) existing
          else if (existing.size < e.limit) {
            val next = inStack(f)
            val newAll = Utils.concat(existing, next)
            m.update(e.zeroed, newAll)
            newAll
          }
          else existing
        }
        else if (breakLoops) Nil
        else {
          val v = inStack(f)
          m.update(e.zeroed, v)
          v
        }
      }
    }


    def logAttempt(name: String)(implicit ctx: ExecCtx): Unit = {
      //c.info(c.enclosingPosition, s"Attempt $name ${ctx.result} \n $ctx", force = true)
    }

    implicit class OptionAdds(o: Seq[Candidate]) {
      def limit(implicit e: ExecCtx): Seq[Candidate] = o.sortBy(_.size).distinct.take(e.limit)

      def warnEmpty(stage: String)(implicit e: ExecCtx): Seq[Candidate] = {
        if (o.isEmpty) {
          //c.info(c.enclosingPosition, s"$stage No implicits $e", force = true)
        }
        o
      }
    }


    object Utils {
      @inline def concat(opts: Seq[Candidate]*)(implicit c: ExecCtx): Seq[Candidate] = opts.flatten.limit

      def transpose[A](s: Seq[Seq[A]]): Seq[Seq[A]] = {
        s match { //Most common cases are resolved without recursion
          case Seq() => Seq(Nil)
          case Seq(h) => h.map(Seq(_))
          case Seq(h, t) => for (sh <- h; st <- t) yield Seq(sh, st)
          case Seq(h, t, r) => for (sh <- h; st <- t; sr <- r) yield Seq(sh, st, sr)
          case h +: t => for(sh <- h; st <- transpose(t)) yield sh +: st
        }
      }
    }


    object ExprCreate extends ExprCreator {

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

    def generateFromCtxFunctions(implicit ctx: ExecCtx): Seq[Candidate] = Cache.cached {
      logAttempt("From func")
      if (ctx.n == 0) Nil
      else {
        val candidates = Timer.timer("Choose correct functions") {
          ctx.ctx.flatMap(_.resultFits(ctx.result))
        }
        val fff = {
          for (c <- candidates) yield {
            val argsTrees =
              c.args.map(ctx.withResult)
                .map(_.decreaseN)
                .foldLeft[List[Seq[Candidate]]](Nil) { //Generate till first failure
                  case (l, t) =>
                    if (l.headOption.exists(_.isEmpty)) l
                    else generateFunc(t) :: l
                }.reverse

            if (argsTrees.exists(_.isEmpty)) Nil
            else {
              val transposed = Utils.transpose(argsTrees)
              val funcExpr = ExprCreate.fromCtxSelect(c.idx)(ctx.withResult(c.wholeType))
              transposed.map(x => c(funcExpr, x))
            }
          }
        }
        Utils.concat(fff: _*).warnEmpty("GF")
      }
    }

    def generateFromArgs(implicit ctx: ExecCtx): Seq[Candidate] = Cache.cached {
      logAttempt("From args")
      ctx.args match { //Can we take result from arguments
        case SingleArg(t) if t <:< ctx.result => Seq(ExprCreate.fromArgsEq)
        case ListArgs(t) =>
          val okArgs = t.zipWithIndex.collect { case (SingleArg(t), i) if t <:< ctx.result => i }
          okArgs.map(ExprCreate.fromArgsSelect).limit
        case CoproductArgs(_) => sys.error("Shouldn't be here")
        case _ => Nil
      }
    }

    def generatePair(implicit ctx: ExecCtx): Seq[Candidate] = Cache.cached {
      logAttempt("from pair")
      if (ctx.result <:< weakTypeOf[(_, _)]) { //Is result a pair ?
        val e1 = generateNormal(ctx.withResult(ctx.result.typeArgs.head))
        if (e1.isEmpty) return Nil
        val e2 = generateNormal(ctx.withResult(ctx.result.typeArgs(1)))
        (for (e1t <- e1; e2t <- e2) yield ExprCreate.pair(e1t, e2t)).limit
      } else Nil
    }

    def generateNormal(implicit ctx: ExecCtx): Seq[Candidate] = Cache.cached {
      val simpleCases = generateFromArgs
      val fromFuncs = generateFromCtxFunctions //Can we generate result from functions from context
      val pairs = generatePair
      Utils.concat(simpleCases, fromFuncs, pairs).warnEmpty("GN")
    }

    def generateFunc(implicit ctx: ExecCtx): Seq[Candidate] = Cache.cached {
      logAttempt("Generate func")
      ctx.result match {
        case Func1Extractor(t, r) => //Result is a function
          t match {
            case t@Func1Extractor(_, _) => //Result argument is a function
              generateFunc(
                ctx.withCtx(typeToFunc(t, 0) ++ ctx.ctx.map(_.incIdx)).withResult(r)
              ).map(ExprCreate.abstractFunc).limit.warnEmpty("GEF1")
            case t => //Result argument is not a function
              ctx.args match {
                case e: SingleArg =>
                  generateFunc {
                    ctx.withArgs(ListArgs(argsFromA(t) :: e :: Nil)).withResult(r)
                  }.map(ExprCreate.abstractValNotH).limit.warnEmpty("GEF2")
                case ListArgs(tl) =>
                  generateFunc {
                    ctx.withArgs(ListArgs(argsFromA(t) +: tl)).withResult(r)
                  }.map(ExprCreate.abstractVal).limit.warnEmpty("GEF3")
                case CoproductArgs(_) => sys.error("Coproduct shouldnt be here")
              }
          }
        case _ => generateNormal(ctx) //Result is not a function
      }
    }

    def generateComposite(implicit ctx: ExecCtx): Seq[Candidate] = Cache.cached {
      logAttempt("Gen composite")
      if (ctx.result <:< weakTypeOf[HList]) {
        val sTypes = split2ArgsRec(ctx.result, Types.hconsType)
        val options = sTypes.map(ctx.withResult).map(generateComposite(_).limit)
        if (options.exists(_.isEmpty)) Nil
        else {
          options.zip(sTypes).foldRight((Seq(ExprCreate.hnil), Types.hnilType)) {
            case ((e, et), (r, rt)) =>
              (for (e1 <- e; r1 <- r) yield
                ExprCreate.hList(e1, r1, TypeTree(et), TypeTree(rt))(ctx.withResult(et :::: rt))
                ).sortBy(_.size).take(ctx.limit) -> (et :::: rt)
          }._1
        }
      } else if (ctx.result <:< Types.cconsType) {
        val a1 = ctx.result.typeArgs.head
        val rest = ctx.result.typeArgs(1)
        val a1Trees = generateComposite(ctx.withResult(a1))
        val restTrees = if (rest <:< Types.cnilType) Nil else generateComposite(ctx.withResult(rest))
        val a1TreesInl = a1Trees.map(ExprCreate.inlResult(_))
        val restTreesInr = restTrees.map(ExprCreate.inrResult(_))
        Utils.concat(a1TreesInl, restTreesInr)
      } else {
        generateFunc
      }
    }

    def generateFromCoproduct(implicit ctx: ExecCtx): Seq[Candidate] = Cache.cached {
      logAttempt("From copro")
      ctx.args match {
        case CoproductArgs(t) =>
          val mapped = t.map(ctx.withArgs).map(generateComposite(_))
          if (mapped.exists(_.isEmpty)) {
            val tt = t.zip(mapped).filter(_._2.isEmpty).map(_._1)
            c.info(c.enclosingPosition, s"No implicit for $ctx Not defined for $tt", force = true)
            Nil
          } else {
            val trees = mapped.zip(t.map(_.wholeType))
            trees.foldRight((Seq(ExprCreate.cnil), Types.cnilType)) { case ((e, t), (f, ft)) =>
              (for (e1 <- e; f1 <- f) yield ExprCreate.coproduct(e1, f1, t, ft)) -> (t +:+: ft)
            }._1
          }
        case _ => generateComposite(ctx)
      }
    }

    def macroImpl[L <: Nat : c.WeakTypeTag, N <: Nat : c.WeakTypeTag, C <: HList : c.WeakTypeTag, A: c.WeakTypeTag, T: c.WeakTypeTag, O <: Options : c.WeakTypeTag]: c.Tree = {
      val ctx = createContext[L, N, C, A, T, O]
      val exprs = Timer.timer("Generation")(generateFromCoproduct(ctx))

      exprs match {
        case Seq() =>
          c.abort(c.enclosingPosition, s"Implicit not found for $ctx")
        case value =>
          val smallestCandidates = value.sortBy(_.size).take(ctx.limit)
          c.info(c.enclosingPosition, s"Candidates count: ${value.size}", force = true)

          val reified = Timer.timer("Tree gen") {
            val deps = smallestCandidates.flatMap(_.allDepesWithItself).distinct.sortBy(_.no)
            val intermediateValueDefs = deps.map {
              _.valDef
            }
            c.info(c.enclosingPosition, s"Deps: " + deps.map(_.no).mkString("\n"), true)
            val ss = c.Expr[Seq[MExpr[C, A, T]]](q"Seq(..${smallestCandidates.map(_.term)})")
            val reified = reify {
              new MGenerator[L, N, C, A, T, O](ss.splice)
            }.tree
            q"""{
                  import _root_.bshapeless.exprs._
                  ..$intermediateValueDefs
                  $reified
               }
               """
          }
          c.info(c.enclosingPosition, Timer.printable, true)
          reified

      }
    }

    override val exprCreate: ExprCreator = ExprCreate
  }

}
