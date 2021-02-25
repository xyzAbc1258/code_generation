package bshapeless

import scala.collection.mutable

class TimerCollector {

  private val m: mutable.Map[String, Long] = mutable.Map.empty

  def timer[T](key: String)(f: => T): T = {
    val s = System.nanoTime()
    val r = f
    val t = System.nanoTime() - s
    m.updateWith(key)(_.map(_ + t).orElse(Some(t)))
    r
  }

  def resultsInMillis: Map[String, Long] = m.view.mapValues(_ / 1000).toMap

  def printable: String = "Timer:\n" + (resultsInMillis.map(s => s"${s._1} - ${s._2}ms").mkString("\n"))
}
