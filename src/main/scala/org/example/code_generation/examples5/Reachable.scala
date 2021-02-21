package org.example.code_generation.examples5

import shapeless._
import shapeless.exprs.Cached2
import shapeless.ops.hlist.Selector

trait Reachable[N <: Nat, Ctx <: HList, Args, Target]

object Reachable {

  case class RAS[N <: Nat, C <: HList, C1 <: HList, A, T](r: Reachable[N, C, A, T])

  object RAS {

    def apply[N <: Nat, C <: HList, C1 <: HList, A, T](): RAS[N, C, C1, A ,T] =
      new RAS[N, C, C1, A ,T](instance)

    implicit def fromRasApp2[N <: Nat, C <: HList, C1 <: HList, A, IM, T](
      implicit e1: Cached2[Reachable[N, C, A, IM]]
    ): RAS[Succ[N], C, (IM => T) :: C1, A, T] = RAS()

    implicit def fromRasApp3[N <: Nat, C <: HList, C1 <: HList, H, A, F, IM, T](
      implicit e1: Cached2[Reachable[N, C, A, IM]],
      e2: Cached2[Reachable[N, C, A, F]]
    ): RAS[Succ[N], C, (F => IM => T) :: C1, A, T] = RAS()

    implicit def fromRasOmit[N <: Nat, C <: HList, C1 <: HList, H, A, T](
      implicit e: RAS[N, C, C1, A, T]
    ): RAS[N, C, H :: C1, A, T] = RAS()

  }

  case class Reachable1[N <: Nat, C <: HList, A, T](r: Reachable[N, C, A, T])

  object Reachable1 {
    def apply[N <: Nat, C <: HList, A, T]() = new Reachable1[N,C,A,T](instance)

    implicit def fromR[N <: Nat, C <: HList, A, T](
      implicit ev: A <:!< Coproduct, e: ReachableApp[N, C, A, T]
    ): Reachable1[N,C,A,T] = apply(e.r)

    implicit def reachCNil[N <: Nat, C <: HList, T]: Reachable1[N, C, CNil, T] = Reachable1()

    implicit def reachCoproduct[N <: Nat, C <: HList, LR, RR <: Coproduct, T](
      implicit el: ReachableApp[N, C, LR, T],
      er: Reachable1[N, C, RR, T]
    ): Reachable1[N, C, LR :+: RR, T] = Reachable1()

  }

  case class ReachableApp[N <: Nat, C <: HList, A, T](r: Reachable[N, C, A, T])

  object ReachableApp {

    def apply[N <: Nat, C <: HList, A, T](): ReachableApp[N, C, A, T] =
      new ReachableApp[N, C, A, T](instance)

    implicit def reachNoApp[N <: Nat, C <: HList, A, T](
      implicit e: T <:!< ((_) => _),
      a: Reachable[N, C, A, T]
    ): ReachableApp[N, C, A, T] = new ReachableApp[N, C, A, T](a)

    implicit def reachApp[N <: Nat, C <: HList, A <: HList, IM, T](
      implicit
      ev: IM <:!< ((_) => _),
      ev2: A <:< HList,
      e: Reachable[N, C, IM :: A, T]
    ): ReachableApp[Succ[N], C, A, IM => T] = ReachableApp()

    implicit def reachAppF[N <: Nat, C <: HList, A, IM, T](
      implicit
      ev: IM <:< ((_) => _),
      e: ReachableApp[N, IM :: C, A, T]
    ): ReachableApp[Succ[N], C, A, IM => T] = ReachableApp()


    implicit def reachAppNH[N <: Nat, C <: HList, A, IM, T](
      implicit
      ev: A <:!< HList,
      e: ReachableApp[N, C, IM :: A :: HNil, T]
    ): ReachableApp[Succ[N], C, A, IM => T] = ReachableApp()

  }

  def instance[N <: Nat, C <: HList, A, T]: Reachable[N, C, A, T] = new Reachable[N, C, A, T] {}

  implicit def reachPair[N <: Nat, C <: HList, A, L, R](
    implicit el: Cached2[Reachable[N, C, A, L]],
    er: Cached2[Reachable[N, C, A, R]]
  ): Reachable[N, C, A, (L, R)] = instance

  implicit def fromList[N <: Nat, C <: HList, A <: HList, T](
    implicit e: Cached2[Selector[A, T]]
  ): Reachable[N, C, A, T] = instance

  implicit def fromArgs[N <: Nat, Ctx <: HList, A, T](
    implicit e: A <:< T
  ): Reachable[N, Ctx, A, T] = instance


  implicit def frosRas[N <: Nat, C <: HList, A, T](
    implicit ev: Cached2[RAS[N, C, C, A, T]]
  ): Reachable[N, C, A, T] = ev.value.r

  implicit def fromCtx[N <: Nat, C <: HList, Args, R](
    implicit ev: R <:< (_) => (_), //Ctx only has functions
    e: Cached2[Selector[C, R]]
  ): Reachable[N, C, Args, R] = instance





  def apply[N <: Nat, C <: HList, A, T](
    implicit e: Reachable1[N, C, A, T]
  ): Reachable[N, C, A, T] = e.r

}
