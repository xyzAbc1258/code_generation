package generation.`implicit`

import generation.`implicit`.Generator._
import generation.exprs.AbstractFunc
import generation.exprs.AbstractVal
import generation.exprs.AbstractValNotH
import generation.exprs.ApplyNative
import generation.exprs.CNilCreate
import generation.exprs.CoproductArgSplit
import generation.exprs.Expr
import generation.exprs.FromArgsEq
import generation.exprs.FromArgsSelect
import generation.exprs.FromCtxSelect
import generation.exprs.HListResultSplit
import generation.exprs.HNilCreate
import generation.exprs.PairExp
import generation.exprs.WithMapCtx
import shapeless._
import shapeless.exprs.Cached2
import shapeless.ops.hlist.{Split => _, _}

class Generator[M <: Mode] {

  /**
   * Abstract class for objects keeping resolved Expressions.
   * There are multiple implementations to provide uniqueness of derivation
   * @tparam N Depth of function calls
   * @tparam Ctx Context in form of list of function signatures which can be used to derive result
   * @tparam A Argument types
   * @tparam R Result type
   */
  trait AbstractGen[N <: Nat, Ctx <: HList, A, R] {
    val e: Set[Expr[Ctx, A, R]]

    def flatMap[G[_ <: Nat, _ <: HList, _, _], A1, R1](f: Expr[Ctx, A, R] => G[N, Ctx, A1, R1])(
      implicit c: AbstractGenCompanion[G]
    ): G[N, Ctx, A1, R1] = c(e.map(f).flatMap(c.unapply(_)).flatten)

    def map[G[_ <: Nat, _ <: HList, _, _], A1, R1](f: Expr[Ctx, A, R] => Expr[Ctx, A1, R1])(
      implicit c: AbstractGenCompanion[G]
    ): G[N, Ctx, A1, R1] = c(e.map(f))

    def to[G[_ <: Nat, _ <: HList, _, _]](implicit c: AbstractGenCompanion[G]): G[N, Ctx, A, R] = c(e)
  }

  /**
   * Companion for AbstractGens
   * @tparam G AbstractGen type
   */
  trait AbstractGenCompanion[G[_ <: Nat, _ <: HList, _, _]] {
    def unapply[N <: Nat, Ctx <: HList, A, R](f: G[N, Ctx, A, R]): Option[Set[Expr[Ctx, A, R]]]

    def apply[N <: Nat, Ctx <: HList, A, R](e: Set[Expr[Ctx, A, R]]): G[N, Ctx, A, R]

    def single[N <: Nat, Ctx <: HList, A, R](e: Expr[Ctx, A, R]): G[N, Ctx, A, R] = apply(Set(e))

    def empty[N <: Nat, Ctx <: HList, A, R]: G[N, Ctx, A, R] = apply(Set())
  }

  /*
   * Generator0 may use Generator2 values which may use Generator1 values.
   */
  case class Generator0[N <: Nat, Ctx <: HList, A, R](e: Set[Expr[Ctx, A, R]]) extends AbstractGen[N, Ctx, A, R]

  //WithMaybe gives us that Maybe will be empty when M is subtype of OnlyOne
  object Generator0 extends WithMaybe[M, OnlyOne] with AbstractGenCompanion[Generator0] {

    implicit val cmp: AbstractGenCompanion[Generator0] = this

    /**
     * Class responsible for splitting R into elements when R is HList
     * @param e Expressions
     * @tparam N Depth of function calls
     * @tparam Ctx Context in form of list of function signatures which can be used to derive result
     * @tparam A Argument types
     * @tparam R Result type
     */
    case class Generator1[N <: Nat, Ctx <: HList, A, R](e: Set[Expr[Ctx, A, R]]) extends AbstractGen[N, Ctx, A, R]

    object Generator1 extends AbstractGenCompanion[Generator1] {

      implicit val cmp: AbstractGenCompanion[Generator1] = this

      implicit def gToG1[N <: Nat, Ctx <: HList, Args, Res](
        implicit ev: Cached2[Res <:!< HList],
        g: Cached2[Generator0[N, Ctx, Args, Res]]
      ): Generator1[N, Ctx, Args, Res] = g.value.to

      implicit def splitResHNil[N <: Nat, Ctx <: HList, Args]: Generator1[N, Ctx, Args, HNil] =
        single(HNilCreate.apply[Ctx, Args])

      implicit def splitRes[N <: Nat, Ctx <: HList, Args, R1, RR <: HList](
        implicit eg1: Generator1[N, Ctx, Args, R1],
        eg2: Generator1[N, Ctx, Args, RR]
      ): Generator1[N, Ctx, Args, R1 :: RR] = for (g1 <- eg1; g2 <- eg2) yield HListResultSplit(g1, g2)
    }

    /**
     * Class responsible for splitting A into cases when A is coproduct
     * @param e
     * @tparam N Depth of function calls
     * @tparam Ctx Context in form of list of function signatures which can be used to derive result
     * @tparam A Argument types
     * @tparam R Result type
     */
    case class Generator2[N <: Nat, Ctx <: HList, A, R](e: Set[Expr[Ctx, A, R]]) extends AbstractGen[N, Ctx, A, R]

    object Generator2 extends AbstractGenCompanion[Generator2] {

      implicit val cmp: AbstractGenCompanion[Generator2] = this

      implicit def g1ToG2[N <: Nat, Ctx <: HList, Args, Res](
        implicit ev: Args <:!< Coproduct,
        g: Cached2[Generator1[N, Ctx, Args, Res]]
      ): Generator2[N, Ctx, Args, Res] = g.value.to

      implicit def splitArgsCNil[N <: Nat, Ctx <: HList, R]: Generator2[N, Ctx, CNil, R] = single(CNilCreate[Ctx, R])

      implicit def splitArgs[N <: Nat, Ctx <: HList, A, AR <: Coproduct, R](
        implicit eg1: Generator1[N, Ctx, A, R],
        eg2: Generator2[N, Ctx, AR, R]
      ): Generator2[N, Ctx, A :+: AR, R] =
        for (g1 <- eg1.to[Generator2]; g2 <- eg2)
          yield CoproductArgSplit(g1, g2)
    }

    /**
     * Class responsible for generation of function calls in expressions
     */
    case class GeneratorS[N <: Nat, Ctx <: HList, C1 <: HList, C2 <: HList, Args, Res](
      f: Split[Ctx, C1, C2] => Set[Expr[Ctx, Args, Res]],
    ) {

      def apply(s: Split[Ctx, C1, C2]): Set[Expr[Ctx, Args, Res]] = f(s)

      def moveLeft[CN <: Nat, H, T <: HList](
        implicit ev: (H :: T) =:= C2
      ): GeneratorS[CN, Ctx, H :: C1, T, Args, Res] = {
        GeneratorS { x => f(x.moveRight.mapRight(ev(_))) }
      }

    }

    object GeneratorS {
      // Iteration by Ctx in GeneratorS

      implicit def fromFuncAppL[N <: Nat, Ctx <: HList, C <: HList, C1 <: HList, Args, IM, R, T](
        implicit //First we need to know what types we can construct,
        evSub: Cached2[M <:!< NoSubtyping],
        ev: T <:< (IM => R),
        eg: Cached2[WrappedPart[N, Ctx, C, C1, Args, IM]],
        egM: Maybe[GeneratorS[N, Ctx, C, T :: C1, Args, R]]
      ): GeneratorS[Succ[N], Ctx, T :: C, C1, Args, R] = GeneratorS(s => {
        val e = FromCtxSelect[Ctx, Args, IM => R](s.selector)
        val tailed = s.mapLeft(_.tail)
        eg.fromSplit(tailed).map(e.app(_)) ++ egM.flatMap(_(s.moveRight))
      })

      implicit def fromFuncAppNoSub[N <: Nat, Ctx <: HList, C <: HList, C1 <: HList, Args, IM, R](
        implicit //First we need to know what types we can construct,
        ev: Cached2[M <:< NoSubtyping],
        eg: Cached2[WrappedPart[N, Ctx, C, C1, Args, IM]],
        egM: Maybe[GeneratorS[N, Ctx, C, (IM => R) :: C1, Args, R]]
      ): GeneratorS[Succ[N], Ctx, (IM => R) :: C, C1, Args, R] = GeneratorS(s => {
        val e = FromCtxSelect[Ctx, Args, IM => R](s.selector)
        val tailed = s.mapLeft(_.tail)
        eg.fromSplit(tailed).map(e.app(_)) ++ egM.flatMap(_(s.moveRight))
      })


      implicit def fromFuncAppL32[N <: Nat, Ctx <: HList, C <: HList, C1 <: HList, Args, IM, IM1, IM2, R](
        implicit //First we need to know what types we can construct,
        eg: Cached2[WrappedPart[N, Ctx, C, C1, Args, IM]],
        eg1: Cached2[WrappedPart[N, Ctx, C, C1, Args, IM1]],
        egM: Maybe[GeneratorS[Succ[N], Ctx, C, (IM => IM1 => R) :: C1, Args, R]]
      ): GeneratorS[Succ[N], Ctx, (IM => IM1 => R) :: C, C1, Args, R] = GeneratorS(s => {
        val e = FromCtxSelect[Ctx, Args, IM => IM1 => R](s.selector)
        val tailed = s.mapLeft(_.tail)
        val e1 = eg.fromSplit(tailed).map(e.app(_))
        eg1.fromSplit(tailed).flatMap(x => e1.map(_.app(x))) ++ egM.flatMap(_(s.moveRight))
      })


      implicit def fromFuncAppH[N <: Nat, Ctx <: HList, C <: HList, C1 <: HList, Args, T, IM, R]( //We skip head
        implicit g: GeneratorS[N, Ctx, C, T :: C1, Args, R]
      ): GeneratorS[N, Ctx, T :: C, C1, Args, R] = g.moveLeft

      // End of iteration
    }

    /**
     * Helper trait used in WrapperPart to generate values using part of context
     * Basically generates values based on context Union[CtxPart1, CtxPart2]#Out
     * @tparam N Depth
     * @tparam Ctx Full context
     * @tparam CtxPart1 Left part of context
     * @tparam CtxPart2 Right part of context
     * @tparam A Arguments
     * @tparam R Result
     */
    trait GeneratorPart[N <: Nat, Ctx <: HList, CtxPart1 <: HList, CtxPart2 <: HList, A, R] {
      def makeExpr(s: Split[Ctx, CtxPart1, CtxPart2]): Set[Expr[Ctx, A, R]]
    }


    object GeneratorPart {
      //Ctx may not be equal Ct when some functions were excluded to avoid repeated use
      implicit def simplePart[C <: Nat, Ct <: HList, Ctx <: HList, A, R](
        implicit eg: Cached2[Generator0[C, Ctx, A, R]]
      ): GeneratorPart[C, Ct, Ctx, HNil, A, R] = {
        (s: Split[Ct, Ctx, HNil]) => eg.e.map(x => WithMapCtx(s.c1, x))
      }

      implicit def simplePart1[C <: Nat, Ct <: HList, T, C1 <: HList, A, R](
        implicit eg: GeneratorPart[C, Ct, T :: C1, HNil, A, R]
      ): GeneratorPart[C, Ct, C1, T :: HNil, A, R] = {
        (s: Split[Ct, C1, T :: HNil]) => eg.makeExpr(s.moveLeft)
      }

      implicit def movedPart2[C <: Nat, Ct <: HList, T1, T2, C1 <: HList, C2 <: HList, A, R](
        implicit eg: GeneratorPart[C, Ct, T1 :: T2 :: C1, C2, A, R]
      ): GeneratorPart[C, Ct, C1, T2 :: T1 :: C2, A, R] = {
        (s: Split[Ct, C1, T2 :: T1 :: C2]) => eg.makeExpr(s.moveLeft.moveLeft)
      }
    }


    /**
     * Helper trait in GeneratorS containing logic of repeated functions.
     * Depending on Mode `M` produces trees which contain or doesnt contain repeated functions
     * @tparam C Depth
     * @tparam Ctx Full context
     * @tparam CP1 Left part of context
     * @tparam CP2 Right part of context
     * @tparam A Arguments
     * @tparam R Result type
     */
    trait WrappedPart[C <: Nat, Ctx <: HList, CP1 <: HList, CP2 <: HList, A, R] {
      def fromSplit(s: Split[Ctx, CP1, CP2]): Set[Expr[Ctx, A, R]]
    }

    object WrappedPart {
      implicit def withoutRepetition[C <: Nat, Ctx <: HList, CP1 <: HList, CP2 <: HList, A, R](
        implicit ev: Cached2[M <:< NoRepeatAppFunction],
        e: Cached2[GeneratorPart[C, Ctx, CP1, CP2, A, R]]
      ): WrappedPart[C, Ctx, CP1, CP2, A, R] = (s: Split[Ctx, CP1, CP2]) => e.value.makeExpr(s)

      implicit def withRepetition[C <: Nat, Ctx <: HList, CP1 <: HList, CP2 <: HList, A, R](
        implicit ev: Cached2[M <:!< NoRepeatAppFunction],
        eg: Cached2[Generator0[C, Ctx, A, R]]
      ): WrappedPart[C, Ctx, CP1, CP2, A, R] = (_: Split[Ctx, CP1, CP2]) => eg.value.e
    }


    implicit def buildPair[N <: Nat, Ctx <: HList, A, L1, L2](
      implicit g1: Cached2[Generator0[N, Ctx, A, L1]],
      g2: Cached2[Generator0[N, Ctx, A, L2]]
    ): Generator0[N, Ctx, A, (L1, L2)] = for (e1 <- g1.value; e2 <- g2.value) yield PairExp(e1, e2)


    implicit def eitherL[N <: Nat, Ctx <: HList, A, RL, RR <: Coproduct](
      implicit g: Generator2[N, Ctx, A, RL]
    ): Generator0[N, Ctx, A, RL :+: RR] = g.map(g => ApplyNative(g)(Inl(_), "Inl"))

    implicit def eitherR[N <: Nat, Ctx <: HList, A, RL, RR <: Coproduct](
      implicit g: Generator2[N, Ctx, A, RR]
    ): Generator0[N, Ctx, A, RL :+: RR] = g.map(g => ApplyNative(g)(Inr(_), "Inr"))


    implicit def fromArgs[N <: Nat, Ctx <: HList, Args <: HList, R](
      implicit //ev: R <:!< ((_) => (_)), //In args theres no functions
      e: Cached2[Selector[Args, R]]
    ): Generator0[N, Ctx, Args, R] = single(FromArgsSelect(e.value))

    implicit def fromArgSet[N <: Nat, Ctx <: HList, L, R](
      implicit ev: L <:< R
    ): Generator0[N, Ctx, L, R] = single(FromArgsEq(ev))

    implicit def fromCtx[N <: Nat, Ctx <: HList, Args, R](
      implicit ev: R <:< (_) => (_), //Ctx only has functions
      e: Cached2[Selector[Ctx, R]]
    ): Generator0[N, Ctx, Args, R] = single(FromCtxSelect(e.value))

    implicit def fromFuncApp[N <: Nat, Ctx <: HList, Args, R](
      implicit gs: GeneratorS[Succ[N], Ctx, Ctx, HNil, Args, R],
      g2: Maybe[Generator0[N, Ctx, Args, R]]
    ): Generator0[Succ[N], Ctx, Args, R] = apply(gs.f(Split.splitAll) ++ g2.flatMap(_.e))

    implicit def appFunc[N <: Nat, Ctx <: HList, Args <: HList, A, R](
      implicit ev: A <:!< ((_) => _),
      eg: Generator0[N, Ctx, A :: Args, R]
    ): Generator0[N, Ctx, Args, A => R] = eg.map(g => AbstractVal(g))

    implicit def appFuncNotHList[N <: Nat, Ctx <: HList, Args, A, R](
      implicit ev: A <:!< ((_) => _),
      ev2: Args <:!< HList,
      eg: Generator0[N, Ctx, A :: Args :: HNil, R]
    ): Generator0[N, Ctx, Args, A => R] = eg.map(g => AbstractValNotH(g))

    implicit def appFuncF[N <: Nat, Ctx <: HList, Args, A, R](
      implicit ev: A <:< ((_) => _),
      eg: Generator0[N, A :: Ctx, Args, R]
    ): Generator0[N, Ctx, Args, A => R] = apply(eg.e.map(g => AbstractFunc(g)))

  }

  def apply[N <: Nat, Ctx <: HList, Args, R](
    implicit g: Lazy[Generator0[N, Ctx, Args, R]]
  ): Enumerate[Expr[Ctx, Args, R]] = Enumerate(g.value.e)


}

object Generator {

  trait Mode

  trait NoRepeatAppFunction extends Mode

  trait OnlyOne extends Mode

  trait NoSubtyping extends Mode

  trait OnlyOneNoRepeat extends NoRepeatAppFunction with OnlyOne

  def apply[M <: Mode] = new Generator[M]()
}