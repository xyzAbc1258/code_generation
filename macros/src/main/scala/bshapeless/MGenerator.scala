package bshapeless

import bshapeless.exprs.{Expr => MExpr}
import shapeless._

import scala.collection.mutable
import scala.language.experimental.macros
import scala.reflect.macros.blackbox

trait Options

trait NoLoops extends Options
trait NoSubtyping extends Options

case class MGenerator[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options](expressions: Seq[MExpr[C, A, T]])

object MGenerator {

  def apply[N <: Nat, C <: HList, A, T](implicit e: MGenerator[Nat._5, N, C, A, T, Options]): MGenerator[Nat._5, N, C, A, T, Options] = e

  def applyO[N <: Nat, C <: HList, A, T, O <: Options](implicit e: MGenerator[Nat._5, N, C, A, T, O]): MGenerator[Nat._5, N, C, A, T, O] = e

  def applyL[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options](implicit e: MGenerator[L, N, C, A, T, O]): MGenerator[L, N, C, A, T, O] = e

  implicit def fromMacro[L <: Nat, N <: Nat, C <: HList, A, T, O <: Options]: MGenerator[L, N, C, A, T, O] = macro MacroImpl.macroImpl[L, N, C, A, T, O]


  class MacroImpl(val c: blackbox.Context) extends GeneratorTypes {

    import c.universe._

    object Cache {

      private val m: mutable.Map[ExecCtx, Set[Candidate]] = mutable.Map.empty

      private val stackHashCodeMap: mutable.Map[Int, List[ExecCtx]] = mutable.Map.empty

      @inline def inStack[T](f: => Set[Candidate])(implicit e: ExecCtx): Set[Candidate] = {
        val hash = e.zeroed.hashCode
        stackHashCodeMap.updateWith(hash)(_ map (e :: _) orElse Some(List(e)))
        val v = f
        stackHashCodeMap.updateWith(hash)(_ map (_.tail))
        v
      }

      def cached(f: => Set[Candidate])(implicit e: ExecCtx): Set[Candidate] = {
        Timer.tick("cached - entry")
        val breakLoops = Timer.timer("loop detection"){
          val zeroed = e.zeroed
          e.noLoops && stackHashCodeMap
            .getOrElse(zeroed.hashCode, Nil)
            .exists(x => x.zeroed == zeroed && !(x eq e))
          }
        val existing: Set[Candidate] = Timer.timer("cache check"){
          val x = m.getOrElse(e.zeroed, {Timer.tick("cache miss"); Set.empty[Candidate]})
          x
        }
        if (breakLoops) existing
        else if (existing.nonEmpty) {
          if (existing.size < e.limit) {
            val next = inStack(f)
            val newAll = Utils.concat(existing, next)
            m.update(e.zeroed, newAll)
            newAll
          }
          else existing
        } else {
          val v = inStack(f)
          m.update(e.zeroed, v)
          v
        }
      }
    }


    def logAttempt(name: String)(implicit ctx: ExecCtx): Unit = {
      //log(s"Attempt $name ${ctx.result} \n $ctx")
    }

    implicit class Extensions(o: Set[Candidate]) {
      def limit(implicit e: ExecCtx): Set[Candidate] = o.toSeq.sortBy(_.size).take(e.limit).toSet

      def warnEmpty(stage: String)(implicit e: ExecCtx): Set[Candidate] = {
        if (o.isEmpty) {
          //log(s"$stage No implicits $e")
        }
        o
      }
    }

    object Utils {

      def concatLazy(opt1: => Set[Candidate], opt2: => Set[Candidate], opt3: => Set[Candidate])(implicit c: ExecCtx): Set[Candidate] = {
        val current1 = opt1
        if(current1.size >= c.limit) return current1.limit
        val current2 = current1 ++ opt2
        if(current2.size >= c.limit) return current2.limit
        (current2 ++ opt3).limit
      }

      @inline def concat(opts:Set[Candidate]*)(implicit c: ExecCtx): Set[Candidate] = opts.toSet.flatten.limit

      def transpose[A](s: Seq[Set[A]]): Set[Seq[A]] = {
        s match { //Most common cases are resolved without recursion
          case Seq() => Set(Nil)
          case Seq(h) => h.map(Seq(_))
          case Seq(h, t) => for (sh <- h; st <- t) yield Seq(sh, st)
          case Seq(h, t, r) => for (sh <- h; st <- t; sr <- r) yield Seq(sh, st, sr)
          case h +: t => for (sh <- h; st <- transpose(t)) yield sh +: st
        }
      }
    }




    def generateFromCtxFunctions(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached {
      logAttempt("From func")
      if (ctx.n == 0) Set.empty
      else {
        val candidates = Timer.timer("Choose correct functions") {
          ctx.ctx.providers.flatMap(_.fittingFunction(ctx.result)).toSet
        }
        val fff = {
          var count = 0
          for (c <- candidates if count < ctx.limit) yield {
            val argsTrees =
              c.args.map(ctx.withResult)
                .map(_.decreaseN)
                .foldLeft[List[Set[Candidate]]](Nil) { //Generate till first failure
                  case (l, t) =>
                    if (l.headOption.exists(_.isEmpty)) l
                    else generateFunc(t) :: l
                }.reverse

            if (argsTrees.exists(_.isEmpty)) Set.empty
            else {
              val transposed = Utils.transpose(argsTrees)
              val funcExpr = ExprCreate.fromCtxSelect(c.idx)(ctx.withResult(c.wholeType))
              val s = transposed.map(x => c(funcExpr, x))
              count += s.size
              s
            }
          }
        }
        fff.flatten.limit.warnEmpty("GF")
      }
    }

    def generateFromArgs(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached {
      logAttempt("From args")
      ctx.args match { //Can we take result from arguments
        case SingleArg(t) if t <:< ctx.result => Set(ExprCreate.fromArgsEq)
        case a: ListArgs => Timer.timer("m_<:<"){
          a.subTypeIndices(ctx.result).map(ExprCreate.fromArgsSelect).toSet
        }
        case CoproductArgs(_) => sys.error("Shouldn't be here")
        case _ => Set.empty
      }
    }

    def generatePair(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached {
      logAttempt("from pair")
      if (ctx.result <:< Types.pairType) { //Is result a pair ?
        val e1 = generateNormal(ctx.withResult(ctx.result.typeArgs.head))
        if (e1.isEmpty) return Set.empty
        val e2 = generateNormal(ctx.withResult(ctx.result.typeArgs(1)))
        (for (e1t <- e1; e2t <- e2) yield ExprCreate.pair(e1t, e2t)).limit
      } else Set.empty
    }

    def generateNormal(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached {
      lazy val simpleCases = generateFromArgs
      lazy val fromFuncs = generateFromCtxFunctions //Can we generate result from functions from context
      lazy val pairs = generatePair
      Utils.concatLazy(simpleCases, fromFuncs, pairs).warnEmpty("GN")
    }

    def generateFunc(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached {
      logAttempt("Generate func")
      ctx.result match {
        case Func1Extractor(t, r) => //Result is a function
          t match {
            case t@Func1Extractor(_, _) => //Result argument is a function
              generateFunc(
                ctx.withCtx(c =>  c.prepend(typeToFuncProvider(t, 0))).withResult(r)
              ).map(ExprCreate.abstractFunc).limit.warnEmpty("GEF1")
            case t => //Result argument is not a function
              ctx.args match {
                case e: SingleArg =>
                  generateFunc {
                    ctx.withArgs(ListArgs(argsFromA(t) :: e :: Nil)).withResult(r)
                  }.map(ExprCreate.abstractValNotH).limit.warnEmpty("GEF2")
                case la: ListArgs =>
                  generateFunc {
                    ctx.withArgs(la.prepend(argsFromA(t))).withResult(r)
                  }.map(ExprCreate.abstractVal).limit.warnEmpty("GEF3")
                case CoproductArgs(_) => sys.error("Coproduct shouldnt be here")
              }
          }
        case _ => generateNormal(ctx) //Result is not a function
      }
    }

    def generateComposite(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached {
      logAttempt("Gen composite")
      if (ctx.result <:< Types.hlistType) {
        val sTypes = Types.split2ArgsRec(ctx.result, Types.hconsType)
        val options = sTypes.map(ctx.withResult).map(generateComposite(_).limit)
        if (options.exists(_.isEmpty)) Set.empty
        else {
          options.zip(sTypes).foldRight((Set(ExprCreate.hnil), Types.hnilType)) {
            case ((e, et), (r, rt)) =>
              (for (e1 <- e; r1 <- r) yield
                ExprCreate.hList(e1, r1, TypeTree(et), TypeTree(rt))(ctx.withResult(et :::: rt))
                ).toSeq.sortBy(_.size).take(ctx.limit).toSet -> (et :::: rt)
          }._1
        }
      } else if (ctx.result <:< Types.cconsType) {
        val a1 = ctx.result.typeArgs.head
        val rest = ctx.result.typeArgs(1)
        val a1Trees = generateComposite(ctx.withResult(a1))
        val restTrees = if (rest <:< Types.cnilType) Set.empty else generateComposite(ctx.withResult(rest))
        val a1TreesInl = a1Trees.map(ExprCreate.inlResult(_))
        val restTreesInr = restTrees.map(ExprCreate.inrResult(_))
        Utils.concat(a1TreesInl, restTreesInr)
      } else {
        generateFunc
      }
    }

    def generateFromCoproduct(implicit ctx: ExecCtx): Set[Candidate] = Cache.cached {
      logAttempt("From copro")
      ctx.args match {
        case CoproductArgs(t) =>
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
        case _ => generateComposite(ctx)
      }
    }

    def macroImpl[L <: Nat : c.WeakTypeTag, N <: Nat : c.WeakTypeTag, C <: HList : c.WeakTypeTag, A: c.WeakTypeTag, T: c.WeakTypeTag, O <: Options : c.WeakTypeTag]: c.Tree = {
      val ctx = createContext[L, N, C, A, T, O]
      val exprs = Timer.timer("Generation")(generateFromCoproduct(ctx))

      exprs match {
        case x if x.isEmpty =>
          c.abort(c.enclosingPosition, s"Implicit not found for $ctx")
        case value =>
          val smallestCandidates = value.toSeq.sortBy(_.size).take(ctx.limit)
          log(s"Candidates count: ${value.size}")

          val reified = Timer.timer("Tree gen") {
            val deps = smallestCandidates.flatMap(_.allDepesWithItself).distinct.sortBy(_.no)
            val intermediateValueDefs = deps.map { _.valDef }
            log(s"Deps: " + deps.map(_.no).mkString("\n"))
            val ss = c.Expr[Seq[MExpr[C, A, T]]](q"Seq(..${smallestCandidates.map(_.term)})")
            val reified = reify {
              new MGenerator[L, N, C, A, T, O](ss.splice)
            }.tree
            q"""{
                  ..$intermediateValueDefs
                  $reified
               }"""
          }
          log(Timer.printable)
          reified

      }
    }
  }

}
