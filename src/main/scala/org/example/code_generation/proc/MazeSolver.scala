package org.example.code_generation.proc


import bshapeless.MGenerator
import org.example.code_generation.examples5.DegenericSquare

import scala.{:: => _}
import shapeless._
import shapeless.ops.hlist.Prepend
import shapeless.ops.nat.Sum

object MazeSolver {
  
  sealed trait B
  sealed trait T extends B
  sealed trait F extends B
  
  type Arr =
    (T:: F:: T:: T:: T:: T:: T:: F:: T:: T:: T::
      T:: T:: F:: T:: F:: T:: T:: T:: F:: T:: T::
      T:: F:: T:: T:: T:: F:: T:: T:: HNil) :: (
    T:: T:: T:: T:: T:: T:: T:: T:: T:: F:: T::
      F:: F:: T:: T:: F:: F:: T:: T:: T:: T:: T::
      T:: T:: T:: T:: F:: F:: F:: T:: HNil) :: (
    T:: T:: T:: T:: T:: T:: T:: F:: T:: F:: T::
      T:: T:: T:: F:: T:: T:: T:: T:: T:: F:: F::
      T:: T:: F:: T:: T:: F:: T:: F:: HNil) :: (
    T:: T:: T:: T:: T:: F:: T:: T:: F:: F:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: F:: T:: T:: T:: T:: F:: HNil) :: (
    T:: T:: T:: T:: T:: F:: T:: T:: F:: F:: T::
      F:: T:: F:: T:: T:: F:: T:: T:: T:: T:: T::
      T:: F:: T:: T:: T:: T:: T:: F:: HNil) :: (
    T:: T:: F:: F:: T:: T:: T:: T:: F:: T:: T::
      T:: T:: T:: F:: T:: T:: T:: F:: T:: T:: T::
      T:: T:: F:: T:: T:: T:: T:: T:: HNil) :: (
    T:: T:: T:: F:: T:: F:: F:: T:: T:: F::
      T:: T:: T:: F:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: HNil) :: (
    T:: T:: T:: F:: T:: F:: F:: T:: T:: F::
      F:: F:: T:: T:: T:: T:: F:: T:: T:: T:: F::
      T:: T:: T:: T:: F:: T:: T:: F:: T:: HNil) :: (
    T:: T:: T:: F:: T:: T:: F:: T:: T:: F:: T::
      F:: T:: T:: F:: F:: F:: T:: F:: T:: T:: T::
      T:: T:: F:: F:: T:: F:: T:: T:: HNil) :: (
    T:: F:: F:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: F:: T:: T:: T:: F:: T:: T:: T:: T:: T::
      T:: T:: F:: F:: T:: F:: T:: T:: HNil) :: (
    T:: F:: T:: F:: T:: T:: F:: T:: T:: T:: T::
      T:: T:: T:: T:: F:: T:: T:: T:: F:: T:: F::
      T:: F:: T:: T:: F:: F:: T:: F:: HNil) :: (
    T:: T:: T:: F:: T:: T:: T:: T:: T:: F:: T::
      T:: T:: T:: T:: F:: T:: T:: F:: F:: T:: F::
      T:: T:: T:: T:: T:: T:: T:: T:: HNil) :: (
    T:: F:: T:: T:: F:: F:: T:: F:: F:: T::
      T:: T:: F:: T:: T:: T:: T:: T:: F:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: T:: HNil) :: (
    T:: T:: T:: F:: T:: T:: F:: T:: T:: T:: T::
      T:: T:: T:: T:: T:: F:: T:: T:: T:: T:: T:: T::
      T:: T:: T:: F:: T:: T:: T:: HNil) :: (
    F:: T:: T:: F:: T:: T:: F:: T:: T:: T:: T::
      T:: F:: T:: T:: F:: T:: T:: T:: F:: T:: T::
      T:: F:: T:: T:: T:: T:: T:: T:: HNil) :: (
    T:: F:: F:: T:: T:: T:: F:: F:: T:: T::
      F:: F:: T:: T:: F:: T:: T:: F:: F:: T:: T::
      T:: T:: T:: T:: T:: F:: T:: T:: T:: HNil) :: (
    T:: T:: F:: F:: T:: T:: T:: T:: T:: T:: T::
      F:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: T:: F:: T:: T:: T:: T:: HNil) :: (
    T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: F::
      F:: T:: T:: T:: F:: F:: F:: T:: F:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: HNil) :: (
    T:: T:: T:: T:: T:: F:: T:: T:: T:: F:: T::
      F:: F:: T:: T:: T:: T:: T:: F:: T:: T:: T::
      T:: T:: T:: T:: T:: F:: F:: T:: HNil) :: (
    F:: F:: T:: T:: F:: T:: F:: T:: T:: F::
      F:: T:: F:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: T:: T:: T:: F:: T:: T:: T:: T:: HNil) :: (
    T:: T:: T:: F:: F:: F:: T:: F:: T:: T::
      T:: T:: T:: F:: T:: T:: T:: T:: T:: T:: T:: T::
      F:: T:: F:: T:: T:: T:: T:: F:: HNil) :: (
    F:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T::
      F:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T:: T::
      T:: T:: F:: T:: F:: F:: T:: HNil) :: (
    T:: T:: T:: T:: T:: F:: T:: T:: T:: T:: T::
      T:: T:: T:: F:: T:: F:: T:: T:: F:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: HNil) :: (
    T:: T:: T:: F:: T:: T:: T:: T:: F:: T:: T::
      F:: T:: T:: T:: T:: T:: F:: T:: T:: F:: T::
      T:: T:: T:: F:: T:: F:: T:: T:: HNil) :: (
    T:: T:: T:: T:: T:: T:: T:: F:: T:: T:: T::
      T:: T:: T:: T:: T:: T:: F:: T:: T:: T:: T:: T::
      T:: T:: F:: F:: T:: T:: T:: HNil) :: (
    T:: T:: T:: F:: T:: T:: F:: T:: T:: T:: T::
      F:: T:: T:: T:: T:: T:: T:: F:: F:: T:: T::
      T:: T:: F:: T:: T:: T:: F:: T:: HNil) :: (
    F:: F:: T:: T:: F:: T:: T:: T:: T:: F::
      T:: T:: T:: F:: T:: T:: F:: F:: T:: T:: T::
      T:: T:: T:: T:: T:: F:: F:: F:: T:: HNil) :: (
    T:: T:: T:: T:: T:: T:: T:: F:: T:: F:: T::
      F:: T:: F:: T:: T:: F:: F:: F:: T:: T:: T::
      T:: T:: T:: T:: T:: T:: T:: T:: HNil) :: (
    T:: T:: F:: T:: F:: T:: T:: T:: T:: T:: F::
      T:: T:: T:: T:: T:: F:: T:: T:: F:: F:: T::
      F:: T:: F:: T:: T:: F:: T:: T:: HNil) :: (
    T:: T:: T:: T:: T:: F:: T:: T:: F:: F::
      F:: T:: T:: F:: F:: T:: F:: F:: T:: T:: T::
      F:: T:: T:: T:: T:: T:: T:: T:: T ::HNil) :: HNil


  trait Pos[R, C]

  type Down[CN <: Nat, RN <: Nat] = Pos[RN, CN] => Pos[Succ[RN], CN]
  type Up[CN <: Nat, RN <: Nat] = Pos[Succ[RN], CN] => Pos[RN, CN]
  type Left[CN <: Nat, RN <: Nat] = Pos[RN, Succ[CN]] => Pos[RN, CN]
  type Right[CN <: Nat, RN <: Nat] = Pos[RN, CN] => Pos[RN, Succ[CN]]

  type Succ2[T <: Nat] = Succ[Succ[T]]

  type L28 = Succ2[Succ2[Succ2[Nat._22]]] ::Succ2[Succ2[Succ[Nat._22]]] :: Succ2[Succ2[Nat._22]] ::Succ[Succ[Succ[Nat._22]]] :: Succ[Succ[Nat._22]] ::Succ[Nat._22] :: Nat._22 ::Nat._21 :: Nat._20 :: Nat._19 :: Nat._18 ::Nat._17 :: Nat._16 ::Nat._15 :: Nat._14 ::Nat._13 :: Nat._12 ::Nat._11 :: Nat._10 :: Nat._9 :: Nat._8 ::Nat._7 :: Nat._6 ::Nat._5 :: Nat._4 ::Nat._3 :: Nat._2 ::Nat._1 :: Nat._0 :: HNil
  type L29 = Succ2[Succ2[Succ2[Succ[Nat._22]]]] :: L28

  val degs2 = DegenericSquare[L29, L29, Pos]

  def main(args: Array[String]): Unit = {
    println(degs2)
  }
}
