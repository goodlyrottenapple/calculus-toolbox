import scala.util.parsing.combinator.{JavaTokenParsers, PackratParsers}
import scala.util.parsing.json._
/*calc_import*/

object Parser extends JavaTokenParsers with PackratParsers {

	lazy val stringParser:PackratParser[List[Char]] = 
		ident ^^ { i => i.toList }

/*/*uncommentL?Structure*/
	lazy val structure_listParser:PackratParser[List[Structure]] =
		"[" ~ "]" ^^ { _ => List[Structure]() } |
		"[" ~> rep(structureParser <~ ",") ~ structureParser <~ "]" ^^ { case list ~ last => list ++ List[Structure](last) }
/*uncommentR?Structure*/*/

/*parser_calc_structure*/

/*parser_calc_structure_rules*/


/*/*uncommentL?core_compiled*/
	lazy val prooftreeListParser : PackratParser[List[Prooftree]] =
		"[" ~ "]" ^^ { _ => List[Prooftree]() } |
		"[" ~> rep(prooftreeParser <~ ",") ~ prooftreeParser <~ "]" ^^ { case list ~ last => list ++ List[Prooftree](last) }

	lazy val prooftreeParser : PackratParser[Prooftree] =
		sequentParser ~ "<==" ~ ruleParser ~ prooftreeListParser ^^ { case a ~ "<==" ~ b ~ c => Prooftreea(a, b, c) } |
		"(" ~> sequentParser ~ "<==" ~ ruleParser ~ prooftreeListParser  <~ ")" ^^ { case a ~ "<==" ~ b ~ c => Prooftreea(a, b, c) }

	def parseProoftree(s:String) : Option[Prooftree] = parseAll(prooftreeParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}
/*uncommentR?core_compiled*/*/

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
