package org.example.code_generation.proc

import bshapeless.MGenerator
import bshapeless.ObjectFuncProvider
import bshapeless.Options
import shapeless._

import scala.collection.immutable

object Replicate {

  trait S[+A]
  case class W(s: String) extends S[Nothing]

  trait SWrapper {
    def wrap[A](a: A): S[A]
  }

  object SimpleSWrapper extends SWrapper {
    override def wrap[A](a: A): S[A] =
      W(a.toString)
  }

  def main(args: Array[String]): Unit = {

    val gen = MGenerator.applyL[
      Nat._1,
    Nat._10,
    ObjectFuncProvider[SWrapper]::HNil,
    SWrapper::Int::HNil,
    S[Int],
    Options
    ]


    for(e <- gen.expressions) {
      println(e(ObjectFuncProvider::HNil, SimpleSWrapper::12::HNil))
    }
  }


  def sum(l: List[Int]): Int = {
    l match {
      case Nil => 0
      case h +: t => h + sum(t)
    }
  }

  def sumTailRec(l: List[Int], acc: Int): Int = {
    l match {
      case h +: t => sumTailRec(t, acc + h)
      case Nil => acc
    }
  }

}
