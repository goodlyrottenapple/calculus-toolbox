import scala.util.parsing.combinator._
import scala.util.parsing.json._
/*calc_import*/

object Parser extends JavaTokenParsers with OperatorPrecedenceParsers {

	lazy val stringParser:PackratParser[List[Char]] = 
		ident ^^ { i => i.toList }


	def listParser[T](innerParser:PackratParser[T]):PackratParser[List[T]] =
		"[" ~ "]" ^^ { _ => List[T]() } |
		"[" ~> rep(innerParser <~ ",") ~ innerParser <~ "]" ^^ { case list ~ last => list ++ List[T](last) }

/*/*uncommentL?Structure*/
	lazy val structure_listParser:PackratParser[List[Structure]] = listParser[Structure](structureParser)
/*uncommentR?Structure*/*/

/*parser_calc_structure*/

/*parser_calc_structure_rules*/


/*/*uncommentL?core_compiled*/
	def prooftreeListParser : Parser[List[Prooftree]] =
		"[" ~ "]" ^^ { _ => List[Prooftree]() } |
		"[" ~> rep(prooftreeParser <~ ",") ~ prooftreeParser <~ "]" ^^ { case list ~ last => list ++ List[Prooftree](last) }

	def prooftreeParser : Parser[Prooftree] =
		sequentParser ~ "<==" ~ "(" ~ ruleParser ~ ")" ~ prooftreeListParser ^^ { case a ~ "<==" ~ "(" ~ b ~ ")" ~ c => Prooftreea(a, b, c) } |
		"(" ~> sequentParser ~ "<==" ~ "(" ~ ruleParser ~ ")" ~ prooftreeListParser  <~ ")" ^^ { case a ~ "<==" ~ "(" ~ b ~ ")" ~ c => Prooftreea(a, b, c) }

	def parseProoftree(s:String) : Option[Prooftree] = parseAll(prooftreeParser,s) match {
		case Success(result, _) => Some(result)
		case NoSuccess(msg, _) => println(msg);None
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
		else if (args.length == 2){
			Some(JSON.parseFull(args(1))) match {
      			case Some(L(list)) =>
      				val buf = new scala.collection.mutable.ListBuffer[String]()
					for (e <- list) parseSequent(e) match {
				    	case Some(r) => 
				    		if(args(0) == "se") buf += PrintCalc.sequentToString(r, PrintCalc.ISABELLE_SE)
				    		else buf += PrintCalc.sequentToString(r, PrintCalc.ISABELLE)
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


/* the following code snippet was adapted from code found at https://gist.github.com/hisui/1692021 */

trait OperatorPrecedenceParsers extends PackratParsers {

  trait Op[+T,U] {
    def lhs:Double = 0
    def rhs:Double = 0
    def parse:PackratParser[T]
  }

  case class Infix[T,U]
  ( override val lhs:Double
  , override val rhs:Double)
  ( override val parse:PackratParser[T])(val map:(T,U,U) => U) extends Op[T,U]

  case class Prefix[T,U](override val rhs:Double)(override val parse:PackratParser[T])(val map:(T,U) => U) extends Op[T,U]
  case class Suffix[T,U](override val lhs:Double)(override val parse:PackratParser[T])(val map:(T,U) => U) extends Op[T,U]

  def operators[T,U](opseq:Op[T,U]*)(innermost:PackratParser[U]) = new PackratParser[U] {

    type Ops = List[(Op[T,U],T)]
    type Out = List[U]

    val (prefixOps, suffixOps) = opseq.partition( _.isInstanceOf[Prefix[_,_]] )

    def findPrefix(ops:Ops, out:Out, in:Input):ParseResult[U] = {

      prefixOps.iterator.map(e => e -> e.parse(in))
        .collectFirst {
          case (op, Success(o, in2)) => findPrefix(op -> o :: ops, out, in2)
        }
        .getOrElse{ //println(innermost(in)); 
        	innermost(in)
          .flatMapWithNext(o => in => findSuffix(ops, o :: out, in)) }
    }
    
    def fold(lhs:Double, ops:Ops, out:Out):(Ops,Out) =
      ops match {
        case (op, o)::ops if op.rhs < lhs =>
          fold(lhs, ops, (( (op, out): @unchecked ) match {
            case (op:Prefix[T,U], x::xs) => op.map(o, x) :: xs
            case (op:Suffix[T,U], x::xs) => op.map(o, x) :: xs
            case (op: Infix[T,U], y::x::xs) => op.map(o, x, y) :: xs
          }))
        case _ => ops -> out
      }

    def findSuffix(ops:Ops, out:Out, in:Input):ParseResult[U] =
      suffixOps.iterator.map(e => e -> e.parse(in))
        .collectFirst {
          case (op, Success(o, in)) =>
            val $ = fold(op.lhs, ops, out)
            (if (op.isInstanceOf[Infix[_,_]])
              findPrefix _ else
              findSuffix _ ) ((op, o) :: $._1, $._2, in)
        }
        .getOrElse(Success(fold(1/0.0, ops, out)._2.head, in))

    override def apply(in:Input):ParseResult[U] = findPrefix(Nil, Nil, in)

  }
}