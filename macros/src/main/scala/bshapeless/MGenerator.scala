package bshapeless

import bshapeless.exprs.{Expr => MExpr}
import shapeless._

import scala.collection.mutable
import scala.reflect.macros.blackbox
import scala.language.experimental.macros

case class MGenerator[L <: Nat, N <: Nat, C <: HList, A, T](expressions: Seq[MExpr[C, A, T]])

object MGenerator {

  def apply[N <: Nat, C <: HList, A, T](implicit e: MGenerator[Nat._5, N, C, A, T]): MGenerator[Nat._5, N, C, A, T] = e

  def applyL[L <: Nat, N <: Nat, C <: HList, A, T](implicit e: MGenerator[L, N, C, A, T]): MGenerator[L, N, C, A, T] = e

  implicit def fromMacro[L <: Nat, N <: Nat, C <: HList, A, T]: MGenerator[L, N, C, A, T] = macro MacroImpl.macroImpl[L, N, C, A, T]


  class MacroImpl(val c: blackbox.Context) extends CommonTypes {

    import c.universe._

    trait Appliable[T] {
      def apply(tycon: T, args: T*): T

      def applyType(tycon: Type, args: T*): T

      def isSubType(t: T, expected: Type): Boolean
    }

    object Cache {

      private val m: mutable.Map[ExecCtx, Option[Seq[Candidate]]] = mutable.Map.empty

      def cached(f: => Option[Seq[Candidate]])(implicit e: ExecCtx): Option[Seq[Candidate]] =
        if (m.getOrElse(e.zeroed, None).exists(_.nonEmpty)) m(e.zeroed)
        else {
          val v = f
          m.update(e.zeroed, v)
          v
        }
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

    def logAttempt(name: String)(implicit ctx: ExecCtx): Unit = {
      c.info(c.enclosingPosition, s"Attempt $name $ctx", force = true)
    }

    implicit class OptionAdds(o: Option[Seq[Candidate]]) {
      def limit(implicit e: ExecCtx): Option[Seq[Candidate]] = o.map(_.sortBy(_.size).take(e.limit))

      def warnEmpty(stage: String)(implicit e: ExecCtx): Option[Seq[Candidate]] = {
        if (o.isEmpty) {
          c.info(c.enclosingPosition, s"$stage No implicits $e", force = true)
        }
        o
      }
    }

    implicit class CommonTypeBuilder[T: Appliable](a2: T) {
      def ::::(a1: T): T = { //Methods ending with colon bind to right eg. t1 :::: t2 == t2.::::(t1)
        assert(Appliable[T].isSubType(a2, weakTypeOf[HList]))
        Appliable[T].applyType(Types.hconsType.typeConstructor, a1, a2)
      }

      def +:+:(a1: T): T = {
        assert(Appliable[T].isSubType(a2, weakTypeOf[Coproduct]))
        Appliable[T].applyType(Types.cconsType.typeConstructor, a1, a2)
      }

      def ==>(a1: T): T =
        Appliable[T].applyType(Types.funcType.typeConstructor, a2, a1)
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


    object Types {
      val hnilType: Type = weakTypeOf[HNil]
      val cnilType: Type = weakTypeOf[CNil]
      val hconsType: Type = weakTypeOf[shapeless.::[_, _]]
      val cconsType: Type = weakTypeOf[:+:[_, _]]
      val funcType: Type = weakTypeOf[(_) => _]
    }

    object ExprCreate {

      def const(n: Int): Tree = Literal(Constant(n))

      def resType(implicit ctx: ExecCtx): Type = ctx.result

      def ttr(t: Type): Tree = TypeTree(t)

      def ctxTypeT(implicit ctx: ExecCtx): Tree = TypeTree(ctx.ctxType)

      def argTypeT(implicit ctx: ExecCtx): Tree = TypeTree(ctx.argType)

      def resTypeT(implicit ctx: ExecCtx): Tree = ttr(ctx.result)

      def hnil(implicit ctx: ExecCtx): Candidate =
        Candidate(q"_root_.bshapeless.exprs.HNilCreate.apply[$ctxTypeT, $argTypeT]", 1)

      def hList(head: Candidate, tail: Candidate, hType: Tree, tType: Tree)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"_root_.bshapeless.exprs.HListResultSplit[$ctxTypeT, $argTypeT, $hType, $tType]($head, $tail)",
          head.size + tail.size + 1
        )

      def cnil(implicit ctx: ExecCtx): Candidate =
        Candidate(q"_root_.bshapeless.exprs.CNilCreate.apply[$ctxTypeT, $resTypeT]", 1)

      def coproduct(h: Candidate, t: Candidate, hType: Tree, tType: Tree)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"_root_.bshapeless.exprs.CoproductArgSplit[$ctxTypeT, $hType, $tType, $resTypeT]($h, $t)",
          h.size + t.size + 1
        )

      def fromArgsSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
        Candidate(q"_root_.bshapeless.exprs.FromArgsSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})", 1)

      def fromArgsEq(implicit ctx: ExecCtx): Candidate =
        Candidate(q"_root_.bshapeless.exprs.FromArgsEq.create[$ctxTypeT, $argTypeT, $resTypeT]", 1)

      def fromCtxSelect(n: Int)(implicit ctx: ExecCtx): Candidate =
        Candidate(q"_root_.bshapeless.exprs.FromCtxSelect[$ctxTypeT, $argTypeT, $resTypeT](${const(n)})", 1)

      def applyExpr(funTree: Candidate, argTree: Candidate, imType: Tree, resultType: Tree)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"_root_.bshapeless.exprs.Apply[$ctxTypeT, $argTypeT, $imType, $resultType]($funTree, $argTree)",
          funTree.size + argTree.size + 1
        )


      def applyNative(exTree: Candidate, fun: Tree, name: String)(implicit ctx: ExecCtx): Candidate =
        Candidate(q"_root_.bshapeless.exprs.ApplyNative($exTree, $fun, $name)", exTree.size + 1)

      def pair(a: Candidate, b: Candidate)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"_root_.bshapeless.exprs.PairExp[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($a, $b)",
          a.size + b.size + 1
        )

      def abstractVal(e: Candidate)(implicit ctx: ExecCtx): Candidate =
        Candidate(
          q"_root_.bshapeless.exprs.AbstractVal[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
          e.size + 1
        )


      def abstractValNotH(e: Candidate)(implicit ctx: ExecCtx): Candidate = Candidate(
        q"_root_.bshapeless.exprs.AbstractValNotH[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
        e.size + 1
      )

      def abstractFunc(e: Candidate)(implicit ctx: ExecCtx): Candidate = Candidate(
        q"_root_.bshapeless.exprs.AbstractFunc[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${ttr(resType.typeArgs(1))}]($e)",
        e.size + 1
      )

      def withMapCtx(f: Tree, e: Tree)(implicit ctx: ExecCtx): Tree =
        q"_root_.bshapeless.exprs.WithMapCtx($f, $e)"

      def inlResult(e: Candidate)(implicit ctx: ExecCtx): Candidate = {
        Candidate(
          q"_root_.bshapeless.exprs.InlResultExpr[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${
            ttr {
              resType.typeArgs(1)
            }
          }]($e)",
          e.size + 1
        )
      }

      def inrResult(e: Candidate)(implicit ctx: ExecCtx): Candidate = {
        Candidate(
          q"_root_.bshapeless.exprs.InrResultExpr[$ctxTypeT, $argTypeT, ${ttr(resType.typeArgs.head)}, ${
            ttr {
              resType.typeArgs(1)
            }
          }]($e)",
          e.size + 1)
      }
    }

    def generateFromCtxFunctions(implicit ctx: ExecCtx): Option[Seq[Candidate]] = Cache.cached {
      logAttempt("From func")
      if (ctx.n == 0) None
      else {
        val smaller = generateFromCtxFunctions(ctx.decreaseN)
        if (smaller.exists(_.size >= ctx.limit)) return smaller.limit
        val candidates = ctx.ctx.filter(_.result <:< ctx.result)
        val fff = {
          var count = smaller.map(_.size).getOrElse(0)
          for (c <- candidates if count < ctx.limit) yield {
            val argsTypes = c.args
            val argsTreesOpt = argsTypes.map(ctx.withResult).map(_.decreaseN).map(generateFunc(_))
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
        Utils.concat((smaller :: fff): _*).warnEmpty("GF")
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
                  ExprCreate.hList(e1, r1, TypeTree(et), TypeTree(rt))).sortBy(_.size).take(ctx.limit), et :::: rt)
            }._1
          )
        }
      } else if (ctx.result <:< weakTypeOf[:+:[_, _]]) {
        val a1 = ctx.result.typeArgs.head
        val rest = ctx.result.typeArgs(1)
        val a1Trees = generateComposite(ctx.withResult(a1))
        val restTrees = if (rest <:< weakTypeOf[CNil]) None
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
                  ExprCreate.coproduct(e1, f1, TypeTree(t), TypeTree(ft))
                )
              ), t +:+: ft)
            }._1)
          }
        case _ => generateComposite(ctx)
      }
    }

    def macroImpl[L <: Nat : c.WeakTypeTag, N <: Nat : c.WeakTypeTag, C <: HList : c.WeakTypeTag, A: c.WeakTypeTag, T: c.WeakTypeTag]: c.Tree = {
      val ctx = createContext[L, N, C, A, T]
      val exprs = generateFromCoproduct(ctx)
      exprs match {
        case Some(value) =>
          val smallest = value.sortBy(_.size).take(ctx.limit).map(_.tree)
          c.info(c.enclosingPosition, s"Candidates count: ${value.size}", force = true)
          val ss = c.Expr[Seq[MExpr[C, A, T]]](q"Seq(..$smallest)")
          reify {
            new MGenerator[L, N, C, A, T](ss.splice)
          }.tree
        case None =>
          c.abort(c.enclosingPosition, s"Implicit not found for $ctx")
      }
    }
  }

}
