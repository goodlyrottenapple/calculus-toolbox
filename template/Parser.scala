import scala.util.parsing.combinator.{JavaTokenParsers, PackratParsers}
import scala.util.parsing.json._
/*calc_import*/

object Parser extends JavaTokenParsers with PackratParsers {

	lazy val stringParser:PackratParser[List[Char]] = 
		ident ^^ { i => i.toList }

/*parser_calc_structure*/

/*parser_calc_structure_rules*/

	def main(args:Array[String]) {
/*/*uncommentL?Sequent*/
		if (args.length == 1){
			Some(JSON.parseFull(args(0))) match {
      			case Some(L(list)) =>
      				val buf = new scala.collection.mutable.ListBuffer[String]()
					for (e <- list) parseSequent(e) match {
				    	case Some(r) => 
				    		buf += PrintCalc.sequentToString(r, PrintCalc.ISABELLE)
				    	case None => buf += ""
				    }
				    print( JSONArray(buf.toList) )
				case _ => print("[]")
		    }
		}  
		else print("[]")
/*uncommentR?Sequent*/*/
	}
}

class CC[T] {
  def unapply(a:Option[Any]):Option[T] = if (a.isEmpty) {
    None
  } else {
    Some(a.get.asInstanceOf[T])
  }
}

object L extends CC[List[String]]
