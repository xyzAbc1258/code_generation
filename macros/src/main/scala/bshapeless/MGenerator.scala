package bshapeless

import bshapeless.exprs.{Expr => MExpr}
import shapeless._

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


    object Timer {

      private val m: mutable.Map[String, Long] = mutable.Map.empty

      def timer[T](key: String)(f: => T): T = {
        val s = System.nanoTime()
        val r = f
        val t = System.nanoTime() - s
        m.updateWith(key)(_.map(_ + t).orElse(Some(t)))
        r
      }

      def resultsInMillis: Map[String, Long] = m.view.mapValues(_ / 1000).toMap

      def printable: String = "Timer:\n" + (resultsInMillis.map(s => s"${s._1} - ${s._2}ms").mkString("\n"))
    }

    object Cache {

      private val m: mutable.Map[ExecCtx, Option[Seq[Candidate]]] = mutable.Map.empty

      private val stack: mutable.Stack[ExecCtx] = mutable.Stack.empty

      def cached(f: => Option[Seq[Candidate]])(implicit e: ExecCtx): Option[Seq[Candidate]] =
        if (m.getOrElse(e.zeroed, None).exists(_.nonEmpty)) m(e.zeroed)
        else if (e.noLoops && stack.exists(x => x.zeroed == e.zeroed && !(x eq e))) {
          //c.info(c.enclosingPosition, s"LOOP ${stack.map(_.result.t.toString).reduce(_ + " -> " + _)} \n $e", true)
          None
        }
        else {
          stack.push(e)
          val v = f
          stack.pop()
          m.update(e.zeroed, v)
          v
        }
    }


    def logAttempt(name: String)(implicit ctx: ExecCtx): Unit = {
      //c.info(c.enclosingPosition, s"Attempt $name ${ctx.result} \n $ctx", force = true)
    }

    implicit class OptionAdds(o: Option[Seq[Candidate]]) {
      def limit(implicit e: ExecCtx): Option[Seq[Candidate]] = o.map(_.sortBy(_.size).take(e.limit))

      def warnEmpty(stage: String)(implicit e: ExecCtx): Option[Seq[Candidate]] = {
        if (o.isEmpty) {
          //c.info(c.enclosingPosition, s"$stage No implicits $e", force = true)
        }
        o
      }
    }


    object Utils {
      def concat(opts: Option[Seq[Candidate]]*)(implicit c: ExecCtx): Option[Seq[Candidate]] =
        Some(opts.flatMap(_.getOrElse(Nil))).filter(_.nonEmpty).limit

      def transpose[A](s: Seq[Seq[A]]): Seq[Seq[A]] = {
        if (s.isEmpty) Seq(Nil)
        else {
          for (sh <- s.head; r <- transpose(s.tail)) yield sh +: r
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
        Candidate(q"HNilCreate.apply[$ctxTypeT, $argTypeT]")(ctx.withResult(Types.hnilType))

      def hList(head: Candidate, tail: Candidate, hType: Tree, tType: Tree)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"HListResultSplit[$ctxTypeT, $argTypeT, $hType, $tType]($head, $tail)",
          head, tail
        )

      def cnil(implicit ctx: ExecCtx): Candidate =
        Candidate(q"CNilCreate.apply[$ctxTypeT, $resTypeT]")(ctx.provider.withArg(Types.cnilType))

      def coproduct(h: Candidate, t: Candidate, hType: Type, tType: Type)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"CoproductArgSplit[$ctxTypeT, ${ttr(hType)}, ${ttr(tType)}, $resTypeT]($h, $t)",
          h, t
        )(ctx.provider.withArg(hType +:+: tType))

      def fromArgsSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
        Candidate(q"FromArgsSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})")

      def fromArgsEq(implicit ctx: ExecCtx): Candidate =
        Candidate(q"FromArgsEq.create[$ctxTypeT, $argTypeT, $resTypeT]")

      def fromCtxSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
        Candidate(q"FromCtxSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})")

      def applyExpr(funTree: Candidate, argTree: Candidate, imType: Tree, resultType: Tree)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"Apply[$ctxTypeT, $argTypeT, $imType, $resultType]($funTree, $argTree)",
          funTree, argTree
        )


      def applyNative(exTree: Candidate, fun: Tree, name: String)(implicit ctx: ExecCtx): Candidate =
        Candidate(q"ApplyNative($exTree, $fun, $name)", exTree)

      def pair(a: Candidate, b: Candidate)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"PairExp[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($a, $b)",
          a, b
        )

      def abstractVal(e: Candidate)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"AbstractVal[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
          e
        )


      def abstractValNotH(e: Candidate)(implicit ctx: ExecCtx): Candidate = Candidate(
        q"AbstractValNotH[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
        e
      )

      def abstractFunc(e: Candidate)(implicit ctx: ExecCtx): Candidate = Candidate(
        q"AbstractFunc[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
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
          e)
      }
    }

    def generateFromCtxFunctions(implicit ctx: ExecCtx): Option[Seq[Candidate]] = Cache.cached {
      logAttempt("From func")
      if (ctx.n == 0) None
      else {
        val smaller: Option[Seq[Candidate]] = None //generateFromCtxFunctions(ctx.decreaseN)
        if (smaller.exists(_.size >= ctx.limit)) return smaller.limit
        val candidates = Timer.timer("Choose correct functions") {
          ctx.ctx.map(_.resultFits(ctx.result)).collect { case Some(x) => x }
        }
        val fff = {
          var count = smaller.map(_.size).getOrElse(0)
          for (c <- candidates if count < ctx.limit) yield {
            val argsTypes = c.args
            val argsTreesOpt = argsTypes.map(ctx.withResult)
              .map(_.decreaseN)
              .foldLeft[List[Option[Seq[Candidate]]]](Nil) { //Generate till first failure
                case (l, t) =>
                  if (l.headOption.exists(_.isEmpty)) l
                  else generateFunc(t) :: l
              }.reverse

            if (argsTreesOpt.exists(_.isEmpty)) None
            else {
              val argsTrees = argsTreesOpt.map(_.get)
              val transposed = Utils.transpose(argsTrees)
              val funcExpr = ExprCreate.fromCtxSelect(c.idx)(ctx.withResult(c.wholeType))
              count += transposed.size
              Some(transposed.map(x => c(funcExpr, x)))
            }
          }
        }
        Utils.concat(smaller :: fff: _*).warnEmpty("GF")
      }
    }

    def generateFromArgs(implicit ctx: ExecCtx): Option[Seq[Candidate]] = Cache.cached {
      logAttempt("From args")
      ctx.args match { //Can we take result from arguments
        case SingleArg(t) if t <:< ctx.result => Some(Seq(ExprCreate.fromArgsEq))
        case ListArgs(t) =>
          val okArgs = t.zipWithIndex.collect { case (SingleArg(t), i) if t <:< ctx.result => i }
          Some(okArgs.map(ExprCreate.fromArgsSelect)).filter(_.nonEmpty).limit
        case CoproductArgs(_) => sys.error("Shouldn't be here")
        case _ => None
      }
    }

    def generatePair(implicit ctx: ExecCtx): Option[Seq[Candidate]] = Cache.cached {
      logAttempt("from pair")
      if (ctx.result <:< weakTypeOf[(_, _)]) { //Is result a pair ?
        val e1 = generateNormal(ctx.withResult(ctx.result.typeArgs.head)).getOrElse(Nil)
        if (e1.isEmpty) return None
        val e2 = generateNormal(ctx.withResult(ctx.result.typeArgs(1))).getOrElse(Nil)
        Option(for (e1t <- e1; e2t <- e2) yield {
          ExprCreate.pair(e1t, e2t)
        }).filter(_.nonEmpty).limit
      } else None
    }

    def generateNormal(implicit ctx: ExecCtx): Option[Seq[Candidate]] = Cache.cached {
      val simpleCases = generateFromArgs
      val fromFuncs = generateFromCtxFunctions //Can we generate result from functions from context
      val pairs = generatePair
      Utils.concat(simpleCases, fromFuncs, pairs).warnEmpty("GN")
    }

    def generateFunc(implicit ctx: ExecCtx): Option[Seq[Candidate]] = Cache.cached {
      logAttempt("Generate func")
      ctx.result match {
        case Func1Extractor(t, r) => //Result is a function
          t match {
            case t@Func1Extractor(_, _) => //Result argument is a function
              generateFunc(
                ctx.withCtx(typeToFunc(t, 0) ++ ctx.ctx.map(_.incIdx)).withResult(r)
              ).map(_ map ExprCreate.abstractFunc).limit.warnEmpty("GEF1")
            case t => //Result argument is not a function
              ctx.args match {
                case e: SingleArg =>
                  generateFunc {
                    ctx.withArgs(ListArgs(argsFromA(t) :: e :: Nil)).withResult(r)
                  }.map(_ map ExprCreate.abstractValNotH).limit.warnEmpty("GEF2")
                case ListArgs(tl) =>
                  generateFunc {
                    ctx.withArgs(ListArgs(argsFromA(t) +: tl)).withResult(r)
                  }.map(_ map ExprCreate.abstractVal).limit.warnEmpty("GEF3")
                case CoproductArgs(_) => sys.error("Coproduct shouldnt be here")
              }
          }
        case _ => generateNormal(ctx) //Result is not a function
      }
    }

    def generateComposite(implicit ctx: ExecCtx): Option[Seq[Candidate]] = Cache.cached {
      logAttempt("Gen composite")
      if (ctx.result <:< weakTypeOf[HList]) {
        val sTypes = split2ArgsRec(ctx.result, Types.hconsType)
        val options = sTypes.map(ctx.withResult).map(generateComposite(_).limit)
        if (options.exists(_.isEmpty)) None
        else {
          Some(
            options.map(_.get).zip(sTypes).foldRight((Seq(ExprCreate.hnil), Types.hnilType)) {
              case ((e, et), (r, rt)) =>
                ((for (e1 <- e; r1 <- r) yield
                  ExprCreate.hList(e1, r1, TypeTree(et), TypeTree(rt))(ctx.withResult(et :::: rt))).sortBy(_.size).take(ctx.limit), et :::: rt)
            }._1
          )
        }
      } else if (ctx.result <:< weakTypeOf[:+:[_, _]]) {
        val a1 = ctx.result.typeArgs.head
        val rest = ctx.result.typeArgs(1)
        val a1Trees = generateComposite(ctx.withResult(a1))
        val restTrees = if (rest <:< Types.cnilType) None
        else generateComposite(ctx.withResult(rest))
        val a1TreesInl = a1Trees.map(_.map(ExprCreate.inlResult(_)))
        val restTreesInr = restTrees.map(_.map(ExprCreate.inrResult(_)))
        Utils.concat(a1TreesInl, restTreesInr)
      } else {
        generateFunc
      }
    }

    def generateFromCoproduct(implicit ctx: ExecCtx): Option[Seq[Candidate]] = Cache.cached {
      logAttempt("From copro")
      ctx.args match {
        case CoproductArgs(t) =>
          val mapped = t.map(ctx.withArgs).map(generateComposite(_))
          if (mapped.exists(_.isEmpty)) {
            val tt = t.zip(mapped).filter(_._2.isEmpty).map(_._1)
            c.info(c.enclosingPosition, s"No implicit for $ctx Not defined for $tt", force = true)
            None
          } else {
            val trees = mapped.map(_.get).zip(t.map(_.wholeType))
            Some(trees.foldRight((Seq(ExprCreate.cnil), Types.cnilType)) { case ((e, t), (f, ft)) =>
              (e.flatMap(e1 =>
                f.map(f1 =>
                  ExprCreate.coproduct(e1, f1, t, ft)
                )
              ), t +:+: ft)
            }._1)
          }
        case _ => generateComposite(ctx)
      }
    }

    def macroImpl[L <: Nat : c.WeakTypeTag, N <: Nat : c.WeakTypeTag, C <: HList : c.WeakTypeTag, A: c.WeakTypeTag, T: c.WeakTypeTag, O <: Options : c.WeakTypeTag]: c.Tree = {
      val ctx = createContext[L, N, C, A, T, O]
      val exprs = Timer.timer("Generation")(generateFromCoproduct(ctx))

      exprs match {
        case Some(value) =>
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
        case None =>
          c.abort(c.enclosingPosition, s"Implicit not found for $ctx")
      }
    }

    override val exprCreate: ExprCreator = ExprCreate
  }

}
