package org.example.code_generation.proc


import bshapeless.NoSubtyping
import bshapeless.ObjectFuncProvider
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
  
  trait Z //= Nat._0
  trait S[Z] // = Succ[Z]

  //import Nat._

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
  type _10 = S[_9]
  type _11 = S[_10]
  type _12 = S[_11]
  type _13 = S[_12]
  type _14 = S[_13]
  type _15 = S[_14]
  type _16 = S[_15]
  type _17 = S[_16]
  type _18 = S[_17]
  type _19 = S[_18]
  type _20 = S[_19]
  type _21 = S[_20]
  type _22 = S[_21]
  type _23 = S[_22]
  type _24 = S[_23]
  type _25 = S[_24]
  type _26 = S[_25]
  type _27 = S[_26]
  type _28 = S[_27]
  type _29 = S[_28]
  type _30 = S[_29]

  type Down[CN , RN] = P[S[RN], CN] => PT[RN, CN] => PT[S[RN], CN]
  type Up[CN , RN] = P[RN, CN] => PT[S[RN], CN] => PT[RN, CN]
  type Left[CN , RN] = P[RN, CN] => PT[RN, S[CN ]] => PT[RN, CN]
  type Right[CN , RN] = P[RN, S[CN]] => PT[RN, CN] => PT[RN, S[CN]]

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



  //val degs9 = DegenericSquare[L9, L9, P, Fold.HList]
  //val degs10 = DegenericSquare[L10, L10, P, Fold.HList]

  //____________
  //|    X X  |
  //|XXX   X  |
  //|X   XXXXX|
  //|X XXX    |
  //|X    X   |
  //|XX  X    | <- here are two possible paths
  //|X   X    |
  //|X XXXXXXX|
  //|X        |

  type Arr2 =
    T::T::T::T::F::T::F::T::T::
    F::F::F::T::T::T::F::T::T::
    F::T::T::T::F::F::F::F::F::
    F::T::F::F::F::T::T::T::T::
    F::T::T::T::T::F::T::T::T::
    F::F::T::T::F::T::T::T::T::
    F::T::T::T::F::T::T::T::T::
    F::T::F::F::F::F::F::F::F::
    F::T::T::T::T::T::T::T::T::HNil




  type Arr16 = P[_0, _0]::P[_0, _1]::P[_0, _2]::P[_0, _3]::P[_0, _4]::P[_0, _6]::P[_0, _7]::P[_0, _8]::P[_0, _10]::P[_0, _11]::P[_0, _13]::P[_0, _14]::P[_0, _16]::P[_1, _0]::P[_1, _1]::P[_1, _4]::P[_1, _6]::P[_1, _8]::P[_1, _11]::P[_1, _13]::P[_1, _14]::P[_1, _15]::P[_1, _16]::P[_2, _4]::P[_2, _8]::P[_2, _10]::P[_2, _11]::P[_2, _15]::P[_2, _16]::P[_3, _0]::P[_3, _1]::P[_3, _2]::P[_3, _3]::P[_3, _4]::P[_3, _5]::P[_3, _6]::P[_3, _7]::P[_3, _8]::P[_3, _10]::P[_3, _13]::P[_3, _14]::P[_3, _15]::P[_3, _16]::P[_4, _1]::P[_4, _4]::P[_4, _10]::P[_4, _11]::P[_4, _13]::P[_4, _16]::P[_5, _0]::P[_5, _1]::P[_5, _4]::P[_5, _11]::P[_5, _13]::P[_5, _14]::P[_5, _15]::P[_5, _16]::P[_6, _0]::P[_6, _3]::P[_6, _4]::P[_6, _9]::P[_6, _10]::P[_6, _11]::P[_6, _15]::P[_6, _16]::P[_7, _0]::P[_7, _3]::P[_7, _6]::P[_7, _7]::P[_7, _8]::P[_7, _9]::P[_7, _13]::P[_7, _14]::P[_7, _15]::P[_7, _16]::P[_8, _0]::P[_8, _2]::P[_8, _3]::P[_8, _6]::P[_8, _9]::P[_8, _12]::P[_8, _13]::P[_8, _15]::P[_8, _16]::P[_9, _0]::P[_9, _2]::P[_9, _6]::P[_9, _8]::P[_9, _9]::P[_9, _15]::P[_9, _16]::P[_10, _0]::P[_10, _2]::P[_10, _3]::P[_10, _4]::P[_10, _5]::P[_10, _6]::P[_10, _8]::P[_10, _10]::P[_10, _11]::P[_10, _12]::P[_10, _15]::P[_10, _16]::P[_11, _0]::P[_11, _6]::P[_11, _8]::P[_11, _9]::P[_11, _10]::P[_11, _12]::P[_11, _13]::P[_11, _14]::P[_11, _15]::P[_11, _16]::P[_12, _0]::P[_12, _4]::P[_12, _5]::P[_12, _6]::P[_12, _9]::P[_12, _16]::P[_13, _0]::P[_13, _1]::P[_13, _2]::P[_13, _3]::P[_13, _8]::P[_13, _9]::P[_13, _10]::P[_13, _11]::P[_13, _12]::P[_13, _13]::P[_13, _14]::P[_13, _15]::P[_13, _16]::P[_14, _0]::P[_14, _3]::P[_14, _4]::P[_14, _5]::P[_14, _13]::P[_14, _15]::P[_14, _16]::P[_15, _0]::P[_15, _1]::P[_15, _2]::P[_15, _5]::P[_15, _6]::P[_15, _7]::P[_15, _8]::P[_15, _10]::P[_15, _11]::P[_15, _12]::P[_15, _13]::P[_15, _15]::P[_15, _16]::HNil

  type up1 = Up[Var1, Var2]
  type down1 = Down[Var1, Var2]
  type left1 = Left[Var1, Var2]
  type right1 = Right[Var1, Var2]

  type Directions1 = right1 :: down1 :: up1 :: left1 ::  HNil

  import shapeless.labelled.FieldType

  type LDirections1 = FieldType["right", right1] :: FieldType["down", down1] :: FieldType["up", up1] :: FieldType["left", left1] :: HNil

  type RightDownDirs = right1 :: down1 :: HNil

  type Arr30 = P[_0, _0]::P[_0, _2]::P[_0, _3]::P[_0, _4]::P[_0, _5]::P[_0, _6]::P[_0, _8]::P[_0, _9]::P[_0, _10]::P[_0, _11]::P[_0, _12]::P[_0, _14]::P[_0, _16]::P[_0, _17]::P[_0, _18]::P[_0, _20]::P[_0, _21]::P[_0, _22]::P[_0, _24]::P[_0, _25]::P[_0, _26]::P[_0, _28]::P[_0, _29]::P[_1, _0]::P[_1, _1]::P[_1, _2]::P[_1, _3]::P[_1, _4]::P[_1, _5]::P[_1, _6]::P[_1, _7]::P[_1, _8]::P[_1, _10]::P[_1, _13]::P[_1, _14]::P[_1, _17]::P[_1, _18]::P[_1, _19]::P[_1, _20]::P[_1, _21]::P[_1, _22]::P[_1, _23]::P[_1, _24]::P[_1, _25]::P[_1, _29]::P[_2, _0]::P[_2, _1]::P[_2, _2]::P[_2, _3]::P[_2, _4]::P[_2, _5]::P[_2, _6]::P[_2, _8]::P[_2, _10]::P[_2, _11]::P[_2, _12]::P[_2, _13]::P[_2, _15]::P[_2, _16]::P[_2, _17]::P[_2, _18]::P[_2, _19]::P[_2, _22]::P[_2, _23]::P[_2, _25]::P[_2, _26]::P[_2, _28]::P[_3, _0]::P[_3, _1]::P[_3, _2]::P[_3, _3]::P[_3, _4]::P[_3, _6]::P[_3, _7]::P[_3, _10]::P[_3, _11]::P[_3, _12]::P[_3, _13]::P[_3, _14]::P[_3, _15]::P[_3, _16]::P[_3, _17]::P[_3, _18]::P[_3, _19]::P[_3, _20]::P[_3, _21]::P[_3, _22]::P[_3, _23]::P[_3, _25]::P[_3, _26]::P[_3, _27]::P[_3, _28]::P[_4, _0]::P[_4, _1]::P[_4, _2]::P[_4, _3]::P[_4, _4]::P[_4, _6]::P[_4, _7]::P[_4, _10]::P[_4, _12]::P[_4, _14]::P[_4, _15]::P[_4, _17]::P[_4, _18]::P[_4, _19]::P[_4, _20]::P[_4, _21]::P[_4, _22]::P[_4, _24]::P[_4, _25]::P[_4, _26]::P[_4, _27]::P[_4, _28]::P[_5, _0]::P[_5, _1]::P[_5, _4]::P[_5, _5]::P[_5, _6]::P[_5, _7]::P[_5, _9]::P[_5, _10]::P[_5, _11]::P[_5, _12]::P[_5, _13]::P[_5, _15]::P[_5, _16]::P[_5, _17]::P[_5, _19]::P[_5, _20]::P[_5, _21]::P[_5, _22]::P[_5, _23]::P[_5, _25]::P[_5, _26]::P[_5, _27]::P[_5, _28]::P[_5, _29]::P[_6, _0]::P[_6, _1]::P[_6, _2]::P[_6, _4]::P[_6, _7]::P[_6, _8]::P[_6, _10]::P[_6, _11]::P[_6, _12]::P[_6, _14]::P[_6, _15]::P[_6, _16]::P[_6, _17]::P[_6, _18]::P[_6, _19]::P[_6, _20]::P[_6, _21]::P[_6, _22]::P[_6, _23]::P[_6, _24]::P[_6, _25]::P[_6, _26]::P[_6, _27]::P[_6, _28]::P[_6, _29]::P[_7, _0]::P[_7, _1]::P[_7, _2]::P[_7, _4]::P[_7, _7]::P[_7, _8]::P[_7, _12]::P[_7, _13]::P[_7, _14]::P[_7, _15]::P[_7, _17]::P[_7, _18]::P[_7, _19]::P[_7, _21]::P[_7, _22]::P[_7, _23]::P[_7, _24]::P[_7, _26]::P[_7, _27]::P[_7, _29]::P[_8, _0]::P[_8, _1]::P[_8, _2]::P[_8, _4]::P[_8, _5]::P[_8, _7]::P[_8, _8]::P[_8, _10]::P[_8, _12]::P[_8, _13]::P[_8, _17]::P[_8, _19]::P[_8, _20]::P[_8, _21]::P[_8, _22]::P[_8, _23]::P[_8, _26]::P[_8, _28]::P[_8, _29]::P[_9, _0]::P[_9, _3]::P[_9, _4]::P[_9, _5]::P[_9, _6]::P[_9, _7]::P[_9, _8]::P[_9, _9]::P[_9, _10]::P[_9, _11]::P[_9, _13]::P[_9, _14]::P[_9, _15]::P[_9, _17]::P[_9, _18]::P[_9, _19]::P[_9, _20]::P[_9, _21]::P[_9, _22]::P[_9, _23]::P[_9, _26]::P[_9, _28]::P[_9, _29]::P[_10, _0]::P[_10, _2]::P[_10, _4]::P[_10, _5]::P[_10, _7]::P[_10, _8]::P[_10, _9]::P[_10, _10]::P[_10, _11]::P[_10, _12]::P[_10, _13]::P[_10, _14]::P[_10, _16]::P[_10, _17]::P[_10, _18]::P[_10, _20]::P[_10, _22]::P[_10, _24]::P[_10, _25]::P[_10, _28]::P[_11, _0]::P[_11, _1]::P[_11, _2]::P[_11, _4]::P[_11, _5]::P[_11, _6]::P[_11, _7]::P[_11, _8]::P[_11, _10]::P[_11, _11]::P[_11, _12]::P[_11, _13]::P[_11, _14]::P[_11, _16]::P[_11, _17]::P[_11, _20]::P[_11, _22]::P[_11, _23]::P[_11, _24]::P[_11, _25]::P[_11, _26]::P[_11, _27]::P[_11, _28]::P[_11, _29]::P[_12, _0]::P[_12, _2]::P[_12, _3]::P[_12, _6]::P[_12, _9]::P[_12, _10]::P[_12, _11]::P[_12, _13]::P[_12, _14]::P[_12, _15]::P[_12, _16]::P[_12, _17]::P[_12, _19]::P[_12, _20]::P[_12, _21]::P[_12, _22]::P[_12, _23]::P[_12, _24]::P[_12, _25]::P[_12, _26]::P[_12, _27]::P[_12, _28]::P[_12, _29]::P[_13, _0]::P[_13, _1]::P[_13, _2]::P[_13, _4]::P[_13, _5]::P[_13, _7]::P[_13, _8]::P[_13, _9]::P[_13, _10]::P[_13, _11]::P[_13, _12]::P[_13, _13]::P[_13, _14]::P[_13, _15]::P[_13, _17]::P[_13, _18]::P[_13, _19]::P[_13, _20]::P[_13, _21]::P[_13, _22]::P[_13, _23]::P[_13, _24]::P[_13, _25]::P[_13, _27]::P[_13, _28]::P[_13, _29]::P[_14, _1]::P[_14, _2]::P[_14, _4]::P[_14, _5]::P[_14, _7]::P[_14, _8]::P[_14, _9]::P[_14, _10]::P[_14, _11]::P[_14, _13]::P[_14, _14]::P[_14, _16]::P[_14, _17]::P[_14, _18]::P[_14, _20]::P[_14, _21]::P[_14, _22]::P[_14, _24]::P[_14, _25]::P[_14, _26]::P[_14, _27]::P[_14, _28]::P[_14, _29]::P[_15, _0]::P[_15, _3]::P[_15, _4]::P[_15, _5]::P[_15, _8]::P[_15, _9]::P[_15, _12]::P[_15, _13]::P[_15, _15]::P[_15, _16]::P[_15, _19]::P[_15, _20]::P[_15, _21]::P[_15, _22]::P[_15, _23]::P[_15, _24]::P[_15, _25]::P[_15, _27]::P[_15, _28]::P[_15, _29]::P[_16, _0]::P[_16, _1]::P[_16, _4]::P[_16, _5]::P[_16, _6]::P[_16, _7]::P[_16, _8]::P[_16, _9]::P[_16, _10]::P[_16, _12]::P[_16, _13]::P[_16, _14]::P[_16, _15]::P[_16, _16]::P[_16, _17]::P[_16, _18]::P[_16, _19]::P[_16, _20]::P[_16, _21]::P[_16, _22]::P[_16, _23]::P[_16, _24]::P[_16, _26]::P[_16, _27]::P[_16, _28]::P[_16, _29]::P[_17, _0]::P[_17, _1]::P[_17, _2]::P[_17, _3]::P[_17, _4]::P[_17, _5]::P[_17, _6]::P[_17, _7]::P[_17, _8]::P[_17, _9]::P[_17, _12]::P[_17, _13]::P[_17, _14]::P[_17, _18]::P[_17, _20]::P[_17, _21]::P[_17, _22]::P[_17, _23]::P[_17, _24]::P[_17, _25]::P[_17, _26]::P[_17, _27]::P[_17, _28]::P[_17, _29]::P[_18, _0]::P[_18, _1]::P[_18, _2]::P[_18, _3]::P[_18, _4]::P[_18, _6]::P[_18, _7]::P[_18, _8]::P[_18, _10]::P[_18, _13]::P[_18, _14]::P[_18, _15]::P[_18, _16]::P[_18, _17]::P[_18, _19]::P[_18, _20]::P[_18, _21]::P[_18, _22]::P[_18, _23]::P[_18, _24]::P[_18, _25]::P[_18, _26]::P[_18, _29]::P[_19, _2]::P[_19, _3]::P[_19, _5]::P[_19, _7]::P[_19, _8]::P[_19, _11]::P[_19, _13]::P[_19, _14]::P[_19, _15]::P[_19, _16]::P[_19, _17]::P[_19, _18]::P[_19, _19]::P[_19, _20]::P[_19, _21]::P[_19, _22]::P[_19, _23]::P[_19, _24]::P[_19, _26]::P[_19, _27]::P[_19, _28]::P[_19, _29]::P[_20, _0]::P[_20, _1]::P[_20, _2]::P[_20, _6]::P[_20, _8]::P[_20, _9]::P[_20, _10]::P[_20, _11]::P[_20, _12]::P[_20, _14]::P[_20, _15]::P[_20, _16]::P[_20, _17]::P[_20, _18]::P[_20, _19]::P[_20, _20]::P[_20, _21]::P[_20, _23]::P[_20, _25]::P[_20, _26]::P[_20, _27]::P[_20, _28]::P[_21, _1]::P[_21, _2]::P[_21, _3]::P[_21, _4]::P[_21, _5]::P[_21, _6]::P[_21, _7]::P[_21, _8]::P[_21, _9]::P[_21, _10]::P[_21, _12]::P[_21, _13]::P[_21, _14]::P[_21, _15]::P[_21, _16]::P[_21, _17]::P[_21, _18]::P[_21, _19]::P[_21, _20]::P[_21, _21]::P[_21, _22]::P[_21, _23]::P[_21, _24]::P[_21, _26]::P[_21, _29]::P[_22, _0]::P[_22, _1]::P[_22, _2]::P[_22, _3]::P[_22, _4]::P[_22, _6]::P[_22, _7]::P[_22, _8]::P[_22, _9]::P[_22, _10]::P[_22, _11]::P[_22, _12]::P[_22, _13]::P[_22, _15]::P[_22, _17]::P[_22, _18]::P[_22, _20]::P[_22, _21]::P[_22, _22]::P[_22, _23]::P[_22, _24]::P[_22, _25]::P[_22, _26]::P[_22, _27]::P[_22, _28]::P[_22, _29]::P[_23, _0]::P[_23, _1]::P[_23, _2]::P[_23, _4]::P[_23, _5]::P[_23, _6]::P[_23, _7]::P[_23, _9]::P[_23, _10]::P[_23, _12]::P[_23, _13]::P[_23, _14]::P[_23, _15]::P[_23, _16]::P[_23, _18]::P[_23, _19]::P[_23, _21]::P[_23, _22]::P[_23, _23]::P[_23, _24]::P[_23, _26]::P[_23, _28]::P[_23, _29]::P[_24, _0]::P[_24, _1]::P[_24, _2]::P[_24, _3]::P[_24, _4]::P[_24, _5]::P[_24, _6]::P[_24, _8]::P[_24, _9]::P[_24, _10]::P[_24, _11]::P[_24, _12]::P[_24, _13]::P[_24, _14]::P[_24, _15]::P[_24, _16]::P[_24, _18]::P[_24, _19]::P[_24, _20]::P[_24, _21]::P[_24, _22]::P[_24, _23]::P[_24, _24]::P[_24, _27]::P[_24, _28]::P[_24, _29]::P[_25, _0]::P[_25, _1]::P[_25, _2]::P[_25, _4]::P[_25, _5]::P[_25, _7]::P[_25, _8]::P[_25, _9]::P[_25, _10]::P[_25, _12]::P[_25, _13]::P[_25, _14]::P[_25, _15]::P[_25, _16]::P[_25, _17]::P[_25, _20]::P[_25, _21]::P[_25, _22]::P[_25, _23]::P[_25, _25]::P[_25, _26]::P[_25, _27]::P[_25, _29]::P[_26, _2]::P[_26, _3]::P[_26, _5]::P[_26, _6]::P[_26, _7]::P[_26, _8]::P[_26, _10]::P[_26, _11]::P[_26, _12]::P[_26, _14]::P[_26, _15]::P[_26, _18]::P[_26, _19]::P[_26, _20]::P[_26, _21]::P[_26, _22]::P[_26, _23]::P[_26, _24]::P[_26, _25]::P[_26, _29]::P[_27, _0]::P[_27, _1]::P[_27, _2]::P[_27, _3]::P[_27, _4]::P[_27, _5]::P[_27, _6]::P[_27, _8]::P[_27, _10]::P[_27, _12]::P[_27, _14]::P[_27, _15]::P[_27, _19]::P[_27, _20]::P[_27, _21]::P[_27, _22]::P[_27, _23]::P[_27, _24]::P[_27, _25]::P[_27, _26]::P[_27, _27]::P[_27, _28]::P[_27, _29]::P[_28, _0]::P[_28, _1]::P[_28, _3]::P[_28, _5]::P[_28, _6]::P[_28, _7]::P[_28, _8]::P[_28, _9]::P[_28, _11]::P[_28, _12]::P[_28, _13]::P[_28, _14]::P[_28, _15]::P[_28, _17]::P[_28, _18]::P[_28, _21]::P[_28, _23]::P[_28, _25]::P[_28, _26]::P[_28, _28]::P[_28, _29]::P[_29, _0]::P[_29, _1]::P[_29, _2]::P[_29, _3]::P[_29, _4]::P[_29, _6]::P[_29, _7]::P[_29, _11]::P[_29, _12]::P[_29, _15]::P[_29, _18]::P[_29, _19]::P[_29, _20]::P[_29, _22]::P[_29, _23]::P[_29, _24]::P[_29, _25]::P[_29, _26]::P[_29, _27]::P[_29, _28]::P[_29, _29]::HNil

  trait MazeTraverser {
    def right[CN, RN](free: P[RN, S[CN]])(current: PT[RN, CN]): PT[RN, S[CN]]
    def down[CN, RN](free: P[S[RN], CN])(current: PT[RN, CN]): PT[S[RN], CN]
    def up[CN, RN](free: P[RN, CN])(current: PT[S[RN], CN]): PT[RN, CN]
    def left[CN, RN](free: P[RN, CN])(current: PT[RN, S[CN]]):PT[RN, CN]
  }

  object MazeTraverser extends MazeTraverser {
    override def right[CN, RN](free: P[RN, S[CN]])(current: PT[RN, CN]): PT[RN, S[CN]] = current.asInstanceOf

    override def down[CN, RN](free: P[S[RN], CN])(current: PT[RN, CN]): PT[S[RN], CN] = current.asInstanceOf

    override def up[CN, RN](free: P[RN, CN])(current: PT[S[RN], CN]): PT[RN, CN] = current.asInstanceOf

    override def left[CN, RN](free: P[RN, CN])(current: PT[RN, S[CN]]): PT[RN, CN] = current.asInstanceOf
  }

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

  /*  val res2 = MGenerator.applyL[
    Nat._1,
    M2._61,
      Directions1,//RightDownDirs,//
      Arr30,//Arr16,//M2.filtered9.Out,//
    PT[_0, _0] => PT[_29, _29], //PT[_15, _8],
    NoLoops with NoSubtyping
    ]
    for(e <- res2.expressions) {
      println(e.stringify("right"::"down"::"up"::"left"::HNil,//"right"::"down"::HNil,//"right"::"down"::HNil,//
        HListUtils.toHList(Range(0, 1000).map(_ => "").toList))(null, null))
    }
*/
    val res3 = MGenerator.applyL[
      Nat._1,
      M2._61,
      ObjectFuncProvider[MazeTraverser]::HNil,//LDirections1,//RightDownDirs,//
      FieldType["traverser",MazeTraverser] :: Arr30,//Arr16,//M2.filtered9.Out,//
      PT[_0, _0] => PT[_29, _29], //PT[_15, _8],
      NoLoops with NoSubtyping
    ]
    res3.expressions
      .map(_.stringify(""::HNil, "traverser"::(Range(1, 1000).foldRight[HList](HNil){case (i, h) => ("field_" + i).toString :: h}))(null, null))
      .foreach(println(_))
  }
}

object M2 {
  import Nat._
  type _23 = shapeless.Succ[_22]
  type _24 = shapeless.Succ[_23]
  type _25 = shapeless.Succ[_24]
  type _26 = shapeless.Succ[_25]
  type _27 = shapeless.Succ[_26]
  type _28 = shapeless.Succ[_27]
  type _29 = shapeless.Succ[_28]
  type _30 = shapeless.Succ[_29]
  type _31 = shapeless.Succ[_30]
  type _32 = shapeless.Succ[_31]
  type _33 = shapeless.Succ[_32]
  type _34 = shapeless.Succ[_33]
  type _35 = shapeless.Succ[_34]
  type _36 = shapeless.Succ[_35]
  type _37 = shapeless.Succ[_36]
  type _38 = shapeless.Succ[_37]
  type _39 = shapeless.Succ[_38]
  type _40 = shapeless.Succ[_39]
  type _41 = shapeless.Succ[_40]
  type _42 = shapeless.Succ[_41]
  type _43 = shapeless.Succ[_42]
  type _44 = shapeless.Succ[_43]
  type _45 = shapeless.Succ[_44]
  type _46 = shapeless.Succ[_45]
  type _47 = shapeless.Succ[_46]
  type _48 = shapeless.Succ[_47]
  type _49 = shapeless.Succ[_48]
  type _50 = shapeless.Succ[_49]
  type _51 = shapeless.Succ[_50]
  type _52 = shapeless.Succ[_51]
  type _53 = shapeless.Succ[_52]
  type _54 = shapeless.Succ[_53]
  type _55 = shapeless.Succ[_54]
  type _56 = shapeless.Succ[_55]
  type _57 = shapeless.Succ[_56]
  type _58 = shapeless.Succ[_57]
  type _59 = shapeless.Succ[_58]
  type _60 = shapeless.Succ[_59]
  type _61 = shapeless.Succ[_60]
  type _62 = shapeless.Succ[_61]
  type _63 = shapeless.Succ[_62]
  type _64 = shapeless.Succ[_63]
  type _65 = shapeless.Succ[_64]
  type _66 = shapeless.Succ[_65]
  type _67 = shapeless.Succ[_66]
  type _68 = shapeless.Succ[_67]
  type _69 = shapeless.Succ[_68]
  type _70 = shapeless.Succ[_69]
  type _71 = shapeless.Succ[_70]
  type _72 = shapeless.Succ[_71]
  type _73 = shapeless.Succ[_72]
  type _74 = shapeless.Succ[_73]
  type _75 = shapeless.Succ[_74]
  type _76 = shapeless.Succ[_75]
  type _77 = shapeless.Succ[_76]
  type _78 = shapeless.Succ[_77]
  type _79 = shapeless.Succ[_78]
  type _80 = shapeless.Succ[_79]

  //val filtered10: Filter[Nothing, Nothing, T] = null//Filter[degs10.Out, Arr2, T]
  //val filtered9 = Filter[degs9.Out, Arr2, T]
}