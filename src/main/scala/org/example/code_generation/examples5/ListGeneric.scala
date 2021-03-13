package org.example.code_generation.examples5

import org.example.code_generation.examples5.Generator.Mode
import shapeless._

object ListGeneric {

  type TMap[T, R] = ((List[T], T => R)) => List[R]
  type TFlatMap[T, R] = ((List[T], (T => List[R]))) => List[R]


  def main(args: Array[String]): Unit = {

    case class Product(items: List[Item])
    case class Item(name: String)

    //val degenMap = Degeneric2[(Item, String)::HNil, TMap]
    //val degenFlatMap = Degeneric2[(Product, Item)::HNil, TFlatMap]
/*
    val g = Generator[Mode][
      Nat._4,
      (Product => List[Item])::
        (Item => String)::
        degenMap.Out::
      degenFlatMap.Out::
      HNil,
      HNil,
    List[Product] => List[String]
    ]
    for(e <- g){
      println(e.stringify(
        "items"::"name"::"map"::"flatMap"::HNil,
        HNil:HNil
      ))
    }*/
  }
}
