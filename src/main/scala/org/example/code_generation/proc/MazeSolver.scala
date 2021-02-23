package org.example.code_generation.proc


import bshapeless.{HListUtils, MGenerator, NoLoops, Var1, Var2}
import bshapeless.degeneric.{DegenericSquare, Filter, Fold}
import org.example.code_generation.proc.MazeSolver._
import shapeless.Nat._4
import shapeless._

import scala.{:: => _}

object MazeSolver {
  
  sealed trait B
  sealed trait T extends B
  sealed trait F extends B
  /*
  type Arr =
    T:: F:: T:: T:: T:: T:: T:: F:: T:: T:: T::
      T:: T:: F:: T:: F:: T:: T:: T:: F:: T:: T::
      T:: F:: T:: T:: T:: F:: T:: T:: 
    T:: T:: T:: T:: T:: T:: T:: T:: T:: F:: T::
      F:: F:: T:: T:: F:: F:: T:: T:: T:: T:: T::
      T:: T:: T:: T:: F:: F:: F:: T:: 
    T:: T:: T:: T:: T:: T:: T:: F:: T:: F:: T::
      T:: T:: T:: F:: T:: T:: T:: T:: T:: F:: F::
      T:: T:: F:: T:: T:: F:: T:: F:: 
    T:: T:: T:: T:: T:: F:: T:: T:: F:: F:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: F:: T:: T:: T:: T:: F:: 
    T:: T:: T:: T:: T:: F:: T:: T:: F:: F:: T::
      F:: T:: F:: T:: T:: F:: T:: T:: T:: T:: T::
      T:: F:: T:: T:: T:: T:: T:: F:: 
    T:: T:: F:: F:: T:: T:: T:: T:: F:: T:: T::
      T:: T:: T:: F:: T:: T:: T:: F:: T:: T:: T::
      T:: T:: F:: T:: T:: T:: T:: T:: 
    T:: T:: T:: F:: T:: F:: F:: T:: T:: F::
      T:: T:: T:: F:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: 
    T:: T:: T:: F:: T:: F:: F:: T:: T:: F::
      F:: F:: T:: T:: T:: T:: F:: T:: T:: T:: F::
      T:: T:: T:: T:: F:: T:: T:: F:: T:: 
    T:: T:: T:: F:: T:: T:: F:: T:: T:: F:: T::
      F:: T:: T:: F:: F:: F:: T:: F:: T:: T:: T::
      T:: T:: F:: F:: T:: F:: T:: T:: 
    T:: F:: F:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: F:: T:: T:: T:: F:: T:: T:: T:: T:: T::
      T:: T:: F:: F:: T:: F:: T:: T:: 
    T:: F:: T:: F:: T:: T:: F:: T:: T:: T:: T::
      T:: T:: T:: T:: F:: T:: T:: T:: F:: T:: F::
      T:: F:: T:: T:: F:: F:: T:: F:: 
    T:: T:: T:: F:: T:: T:: T:: T:: T:: F:: T::
      T:: T:: T:: T:: F:: T:: T:: F:: F:: T:: F::
      T:: T:: T:: T:: T:: T:: T:: T:: 
    T:: F:: T:: T:: F:: F:: T:: F:: F:: T::
      T:: T:: F:: T:: T:: T:: T:: T:: F:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: T:: 
    T:: T:: T:: F:: T:: T:: F:: T:: T:: T:: T::
      T:: T:: T:: T:: T:: F:: T:: T:: T:: T:: T:: T::
      T:: T:: T:: F:: T:: T:: T:: 
    F:: T:: T:: F:: T:: T:: F:: T:: T:: T:: T::
      T:: F:: T:: T:: F:: T:: T:: T:: F:: T:: T::
      T:: F:: T:: T:: T:: T:: T:: T:: 
    T:: F:: F:: T:: T:: T:: F:: F:: T:: T::
      F:: F:: T:: T:: F:: T:: T:: F:: F:: T:: T::
      T:: T:: T:: T:: T:: F:: T:: T:: T:: 
    T:: T:: F:: F:: T:: T:: T:: T:: T:: T:: T::
      F:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: T:: F:: T:: T:: T:: T:: 
    T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: F::
      F:: T:: T:: T:: F:: F:: F:: T:: F:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: 
    T:: T:: T:: T:: T:: F:: T:: T:: T:: F:: T::
      F:: F:: T:: T:: T:: T:: T:: F:: T:: T:: T::
      T:: T:: T:: T:: T:: F:: F:: T:: 
    F:: F:: T:: T:: F:: T:: F:: T:: T:: F::
      F:: T:: F:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: T:: T:: T:: F:: T:: T:: T:: T:: 
    T:: T:: T:: F:: F:: F:: T:: F:: T:: T::
      T:: T:: T:: F:: T:: T:: T:: T:: T:: T:: T:: T::
      F:: T:: F:: T:: T:: T:: T:: F:: 
    F:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T::
      F:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: T:: F:: T:: F:: F:: T:: 
    T:: T:: T:: T:: T:: F:: T:: T:: T:: T:: T::
      T:: T:: T:: F:: T:: F:: T:: T:: F:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: 
    T:: T:: T:: F:: T:: T:: T:: T:: F:: T:: T::
      F:: T:: T:: T:: T:: T:: F:: T:: T:: F:: T::
      T:: T:: T:: F:: T:: F:: T:: T:: 
    T:: T:: T:: T:: T:: T:: T:: F:: T:: T:: T::
      T:: T:: T:: T:: T:: T:: F:: T:: T:: T:: T:: T::
      T:: T:: F:: F:: T:: T:: T:: 
    T:: T:: T:: F:: T:: T:: F:: T:: T:: T:: T::
      F:: T:: T:: T:: T:: T:: T:: F:: F:: T:: T::
      T:: T:: F:: T:: T:: T:: F:: T:: 
    F:: F:: T:: T:: F:: T:: T:: T:: T:: F::
      T:: T:: T:: F:: T:: T:: F:: F:: T:: T:: T::
      T:: T:: T:: T:: T:: F:: F:: F:: T:: 
    T:: T:: T:: T:: T:: T:: T:: F:: T:: F:: T::
      F:: T:: F:: T:: T:: F:: F:: F:: T:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: 
    T:: T:: F:: T:: F:: T:: T:: T:: T:: T:: F::
      T:: T:: T:: T:: T:: F:: T:: T:: F:: F:: T::
      F:: T:: F:: T:: T:: F:: T:: T:: 
    T:: T:: T:: T:: T:: F:: T:: T:: F:: F::
      F:: T:: T:: F:: F:: T:: F:: F:: T:: T:: T::
      F:: T:: T:: T:: T:: T:: T:: T:: T :: HNil
*/

  trait P[R, C]
  trait PT[R, C]
  
  trait Z
  trait S[Z]
  
  type _0 = Z
  type _1 = S[_0]
  type _2 = S[_1]
  type _3 = S[_2]
  type _4 = S[_3]
  type _5 = S[_4]
  type _6 = S[_5]
  type _7 = S[_6]
  type _8 = S[_7]
  type _9 = S[_8]
  
  type Down[CN , RN ] = ((P[RN, CN], P[S[RN], CN])) => PT[RN, CN] => PT[S[RN], CN]
  type Up[CN , RN ] = ((P[S[RN], CN], P[RN, CN])) => PT[S[RN], CN] => PT[RN, CN]
  type Left[CN , RN ] = ((P[RN, S[CN]], P[RN, CN])) => PT[RN, S[CN]] => PT[RN, CN]
  type Right[CN , RN ] = ((P[RN, CN], P[RN, S[CN]])) => PT[RN, CN] => PT[RN, S[CN]]

  type L5 = _4 :: _3 :: _2 :: _1 :: _0 :: HNil
  type L9 = _8 :: _7 :: _6 :: _5 :: L5
  type L10 = _9 :: L9
/*
  val degs5 = DegenericSquare[L5, L5, P, Fold.HList]

  type Arr =
    T :: T :: T :: T :: F ::
    F :: F :: F :: T :: F ::
    F :: T :: T :: T :: F ::
    F :: T :: F :: F :: F ::
    F :: T :: T :: T :: T :: HNil


  val filtered5 = Filter[degs5.Out, Arr, T]
*/



  val degs9 = DegenericSquare[L9, L9, P, Fold.HList]
  //val degs10 = DegenericSquare[L10, L10, P, Fold.HList]

  //____________
  //|    X X   |
  //|XXX   X   |
  //|X   XXXXX |
  //|X XXX     |
  //|X    X    |
  //|          |
  //|XXX X     |
  //|X   X     |
  //|X XXXXXXXX|
  //|X         |

  type Arr2 =
    T::T::T::T::F::T::F::T::T::
    F::F::F::T::T::T::F::T::T::
    F::T::T::T::F::F::F::F::F::
    F::T::F::F::F::T::T::T::T::
    F::T::T::T::T::F::T::T::T::
    F::F::F::T::F::T::T::T::T::
    F::T::T::T::F::T::T::T::T::
    F::T::F::F::F::F::F::F::F::
    F::T::T::T::T::T::T::T::T::HNil



  type up1 = Up[Var1, Var2]
  type down1 = Down[Var1, Var2]
  type left1 = Left[Var1, Var2]
  type right1 = Right[Var1, Var2]

  type Directions1 = up1 :: down1 :: left1 :: right1 ::HNil

  def main(args: Array[String]): Unit = {
    /*val res = MGenerator.applyO[
      Nat._15,
      Directions1,
      filtered5.Out,
      PT[_0, _0] => PT[_4, _4],
      NoLoops
    ]
    for(e <- res.expressions) {
      println(e.stringify("up"::"down"::"left"::"right"::HNil,
        ""::""::""::""::""::""::""::""::""::""::""::""::""::HNil))
    }*/

    val res2 = MGenerator.applyL[
    Nat._1,
    Succ[Succ[Succ[Succ[Succ[Succ[Nat._22]]]]]],
    Directions1,
    M2.filtered9.Out,
    PT[_0, _0] => PT[_8, _8],
    NoLoops
    ]
    for(e <- res2.expressions) {
      println(e.stringify("up"::"down"::"left"::"right"::HNil,
        HListUtils.toHList(Range(0, 100).map(_ => "").toList))(implicitly, null))
    }

  }
}

object M2 {
  val filtered9 = Filter[degs9.Out, Arr2, T]
}