package org.example.code_generation.examples5

import shapeless._
import shapeless.ops.hlist.{Split => _, _}
import Generator._
import bshapeless.exprs.{AbstractFunc, AbstractVal, AbstractValNotH, ApplyNative, CNilCreate, CoproductArgSplit, Expr, FromArgsEq, FromArgsSelect, FromCtxSelect, HListResultSplit, HNilCreate, PairExp, WithMapCtx}
import shapeless.exprs.{Cached2}

class Generator[M <: Mode] {

  case class Generator0[N <: Nat, Ctx <: HList, A, R](e: Set[Expr[Ctx, A, R]])

  object Generator0 extends WithMaybe[M, OnlyOne] {

    case class Generator1[N <: Nat, Ctx <: HList, A, R](e: Set[Expr[Ctx, A, R]])

    object Generator1 {
      implicit def gToG1[N <: Nat, Ctx <: HList, Args, Res](
        implicit ev: Cached2[Res <:!< HList],
        g: Cached2[Generator0[N, Ctx, Args, Res]]
      ): Generator1[N, Ctx, Args, Res] = Generator1(g.value.e)

      implicit def splitResHNil[N <: Nat, Ctx <: HList, Args]: Generator1[N, Ctx, Args, HNil] =
        Generator1(Set(HNilCreate.apply[Ctx, Args]))

      implicit def splitRes[N <: Nat, Ctx <: HList, Args, R1, RR <: HList](
        implicit eg1: Generator1[N, Ctx, Args, R1],
        eg2: Generator1[N, Ctx, Args, RR]
      ): Generator1[N, Ctx, Args, R1 :: RR] = Generator1 {
        for (g1 <- eg1.e; g2 <- eg2.e) yield {
          HListResultSplit(g1, g2)
        }
      }
    }

    case class Generator2[N <: Nat, Ctx <: HList, A, R](e: Set[Expr[Ctx, A, R]])

    object Generator2 {

      implicit def g1ToG2[N <: Nat, Ctx <: HList, Args, Res](
        implicit ev: Args <:!< Coproduct,
        g: Cached2[Generator1[N, Ctx, Args, Res]]
      ): Generator2[N, Ctx, Args, Res] = Generator2(g.value.e)

      implicit def splitArgsCNil[N <: Nat, Ctx <: HList, R]: Generator2[N, Ctx, CNil, R] =
        Generator2(Set(CNilCreate.apply[Ctx, R]))

      implicit def splitArgs[N <: Nat, Ctx <: HList, A, AR <: Coproduct, R](
        implicit eg1: Generator1[N, Ctx, A, R],
        eg2: Generator2[N, Ctx, AR, R]
      ): Generator2[N, Ctx, A :+: AR, R] = Generator2 {
        for (g1 <- eg1.e; g2 <- eg2.e) yield
          CoproductArgSplit(g1, g2)
      }
    }

    case class GeneratorS[N <: Nat, Ctx <: HList, C1 <: HList, C2 <: HList, Args, Res](
      f: Split[Ctx, C1, C2] => Set[Expr[Ctx, Args, Res]],
    ) {

      def moveLeft[CN <: Nat, H, T <: HList](
        implicit ev: C2 =:= (H :: T)
      ): GeneratorS[CN, Ctx, H :: C1, T, Args, Res] = {
        GeneratorS{x => f(x.moveRight.asInstanceOf[Split[Ctx, C1, C2]])}
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
        val e = FromCtxSelect[Ctx, Args, IM => R](s.selector[IM => R, T, C])
        eg.value.fromSplit(s.mapLeft(_.tail)).map(x => e.app(x)) ++
          egM.v.map(_.f(s.moveRight)).getOrElse(Set.empty)
      })

      implicit def fromFuncAppNoSub[N <: Nat, Ctx <: HList, C <: HList, C1 <: HList, Args, IM, R](
        implicit //First we need to know what types we can construct,
        ev: Cached2[M <:< NoSubtyping],
        eg: Cached2[WrappedPart[N, Ctx, C, C1, Args, IM]],
        egM: Maybe[GeneratorS[N, Ctx, C, (IM => R) :: C1, Args, R]]
      ): GeneratorS[Succ[N], Ctx, (IM => R) :: C, C1, Args, R] = GeneratorS(s => {
        val e = FromCtxSelect[Ctx, Args, IM => R](s.selector[IM => R, IM => R, C])
        val tailed = s.mapLeft(_.tail)
        eg.value.fromSplit(tailed).map(x => e.app(x)) ++ egM.v.map(_.f(s.moveRight)).getOrElse(Set.empty)
      })


      implicit def fromFuncAppL32[N <: Nat, Ctx <: HList, C <: HList, C1 <: HList, Args, IM, IM1, IM2, R](
        implicit //First we need to know what types we can construct,
        eg: Cached2[WrappedPart[N, Ctx, C, C1, Args, IM]],
        eg1: Cached2[WrappedPart[N, Ctx, C, C1, Args, IM1]],
        egM: Maybe[GeneratorS[Succ[N], Ctx, C, (IM => IM1 => R) :: C1, Args, R]]
      ): GeneratorS[Succ[N], Ctx, (IM => IM1 => R) :: C, C1, Args, R] = GeneratorS(s => {
        val e = FromCtxSelect[Ctx, Args, IM => IM1 => R](s.selector[IM => IM1 => R, IM => IM1 => R, C])
        val tailed = s.mapLeft(_.tail)
        val e1 = eg.value.fromSplit(tailed).map(x => e.app(x))
        eg1.value.fromSplit(tailed).flatMap(x => e1.map(e => e.app(x))) ++
          egM.v.map(_.f(s.moveRight)).getOrElse(Set.empty)
      })


      implicit def fromFuncAppH[N <: Nat, Ctx <: HList, C <: HList, C1 <: HList, Args, T, IM, R]( //We skip head
        implicit g: GeneratorS[N, Ctx, C, T :: C1, Args, R]
      ): GeneratorS[N, Ctx, T :: C, C1, Args, R] = g.moveLeft

      // End of iteration
    }

    trait GeneratorPart[N <: Nat, Ctx <: HList, CtxPart1 <: HList, CtxPart2 <: HList, A, R] {
      def makeExpr(s: Split[Ctx, CtxPart1, CtxPart2]): Set[Expr[Ctx, A, R]]
    }

    object GeneratorPart {
      implicit def simplePart[C <: Nat, Ct <: HList, Ctx <: HList, A, R](
        implicit eg: Cached2[Generator0[C, Ctx, A, R]]
      ): GeneratorPart[C, Ct, Ctx, HNil, A, R] = {
        (s: Split[Ct, Ctx, HNil]) => eg.value.e.map(x => WithMapCtx(s.c1, x))
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


    trait WrappedPart[C <: Nat, Ctx <: HList, CP1 <: HList, CP2 <: HList, A, R] {
      def fromSplit(s: Split[Ctx, CP1, CP2]): Set[Expr[Ctx, A, R]]
    }

    object WrappedPart {
      implicit def withoutRepetition[C <: Nat, Ctx <: HList, CP1 <: HList, CP2 <: HList, A, R](
        implicit ev: Cached2[M <:< NoRepeatAppFunction],
        e: Cached2[GeneratorPart[C, Ctx, CP1, CP2, A, R]]
      ): WrappedPart[C, Ctx, CP1, CP2, A, R] = {
        (s: Split[Ctx, CP1, CP2]) => e.value.makeExpr(s)
      }

      implicit def withRepetition[C <: Nat, Ctx <: HList, CP1 <: HList, CP2 <: HList, A, R](
        implicit ev: Cached2[M <:!< NoRepeatAppFunction],
        eg: Cached2[Generator0[C, Ctx, A, R]]
      ): WrappedPart[C, Ctx, CP1, CP2, A, R] =
        (_: Split[Ctx, CP1, CP2]) => eg.value.e
    }


    implicit def buildPair[N <: Nat, Ctx <: HList, A, L1, L2](
      implicit g1: Cached2[Generator0[N, Ctx, A, L1]],
      g2: Cached2[Generator0[N, Ctx, A, L2]]
    ): Generator0[N, Ctx, A, (L1, L2)] = Generator0 {
      for (e1 <- g1.value.e; e2 <- g2.value.e) yield {
        PairExp(e1, e2)
      }
    }


    implicit def eitherL[N <: Nat, Ctx <: HList, A, RL, RR <: Coproduct](
      implicit g: Generator2[N, Ctx, A, RL]
    ): Generator0[N, Ctx, A, RL :+: RR] = Generator0 {
      g.e.map(g => ApplyNative[Ctx, A, RL, RL :+: RR](g)(Inl(_), "Inl"))
    }

    implicit def eitherR[N <: Nat, Ctx <: HList, A, RL, RR <: Coproduct](
      implicit g: Generator2[N, Ctx, A, RR]
    ): Generator0[N, Ctx, A, RL :+: RR] = Generator0 {
      g.e.map(g => ApplyNative[Ctx, A, RR, RL :+: RR](g)(Inr(_), "Inr"))
    }


    implicit def fromArgs[N <: Nat, Ctx <: HList, Args <: HList, R](
      implicit //ev: R <:!< ((_) => (_)), //In args theres no functions
      e: Cached2[Selector[Args, R]]
    ): Generator0[N, Ctx, Args, R] =
      Generator0(Set(FromArgsSelect(e.value)))

    implicit def fromArgSet[N <: Nat, Ctx <: HList, L, R](
      implicit ev: L <:< R
    ): Generator0[N, Ctx, L, R] =
      Generator0(Set(FromArgsEq(ev)))

    implicit def fromCtx[N <: Nat, Ctx <: HList, Args, R](
      implicit ev: R <:< (_) => (_), //Ctx only has functions
      e: Cached2[Selector[Ctx, R]]
    ): Generator0[N, Ctx, Args, R] =
      Generator0(Set(FromCtxSelect(e.value)))

    implicit def fromFuncApp[N <: Nat, Ctx <: HList, Args, R](
      implicit gs: GeneratorS[Succ[N], Ctx, Ctx, HNil, Args, R],
      g2: Maybe[Generator0[N, Ctx, Args, R]]
    ): Generator0[Succ[N], Ctx, Args, R] =
      Generator0(gs.f(Split.splitAll) ++ g2.getOrElse(Generator0(Set())).e)

    implicit def appFunc[N <: Nat, Ctx <: HList, Args <: HList, A, R](
      implicit ev: A <:!< ((_) => _),
      eg: Generator0[N, Ctx, A :: Args, R]
    ): Generator0[N, Ctx, Args, A => R] =
      Generator0(eg.e.map(g => AbstractVal(g)))

    implicit def appFuncNotHList[N <: Nat, Ctx <: HList, Args, A, R](
      implicit ev: A <:!< ((_) => _),
      ev2: Args <:!< HList,
      eg: Generator0[N, Ctx, A :: Args :: HNil, R]
    ): Generator0[N, Ctx, Args, A => R] =
      Generator0(eg.e.map(g => AbstractValNotH(g)))


    implicit def appFuncF[N <: Nat, Ctx <: HList, Args, A, R](
      implicit ev: A <:< ((_) => _),
      eg: Generator0[N, A :: Ctx, Args, R]
    ): Generator0[N, Ctx, Args, A => R] =
      Generator0(eg.e.map(g => AbstractFunc(g)))

  }


  def apply[N <: Nat, Ctx <: HList, Args, R](
    implicit g: Lazy[Generator0.Generator2[N, Ctx, Args, R]]
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