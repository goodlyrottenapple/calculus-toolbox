import scala.collection.mutable.ListBuffer
/*calc_import*/

object Proofsearch{
	def derAllAux(s:Sequent, ruleLst:List[Rule]) : List[(Rule, List[Sequent])] = 
		for (rule <- ruleLst) yield der(rule, s)

	def derAll(s:Sequent) : List[(Rule, List[Sequent])] = { derAllAux(s, ruleList).filter{ case (r,l) => r != Fail()} }

	def derTrees(n:Int, seq:Sequent, prems:List[Sequent] = List()) : List[Prooftree] = n match {
		case 0 => List[Prooftree]()
		case n => 
			prems.find(_ ==seq) match {
				case Some(r) => return List(Zer(seq,Prem()))
				case None => 
			}
			var ret = new ListBuffer[Prooftree]()
			for( (rule, derList) <- derAll(seq) ) {
				rule match {
					case RuleZera(r) => ret+= Zer(seq, r) 
					case RuleUa(r) => 
						for(possibleDer <- derTrees(n-1, derList(0), prems) ) {
							ret += Unary(seq, r, possibleDer)
						}
					case RuleDispa(r) => 
						for(possibleDer <- derTrees(n-1, derList(0), prems) ) {
							ret += Display(seq, r, possibleDer)
						}
					case RuleOpa(r) => 
						for(possibleDer <- derTrees(n-1, derList(0), prems) ) {
							ret += Operational(seq, r, possibleDer)
						}
					case RuleBina(r) => 
						for(possibleDer0 <- derTrees(n-1, derList(0), prems);  possibleDer1 <- derTrees(n-1, derList(1), prems)) {
							ret += Binary(seq, r, possibleDer0, possibleDer1)
						}
					case _ => ;
				}
			}
			return ret.toList
	}

	def derTree(max:Int, seq:Sequent, prems:List[Sequent] = List(), n:Int = 0) : Option[Prooftree] = {
		if (n > max) None
		else derTrees(n, seq, prems) match {
			case Nil => derTree(max, seq, prems, n+1)
			case res => Some(res(0))
		}
	}

	def main(args:Array[String]) {
/*	    Parser.parseS("y |- x >>z") match {
	    	case Some(res) => 
	    		println(derAll(res))

	    		derTree(5,res, List(res)) match {
	    			case Some(r)=> println(r)
	    			case _ => println("not found")
	    		}

	    }
*/
	    //println(derAll(seq))
	    //println("\n\n\n")
	    
	}


}

