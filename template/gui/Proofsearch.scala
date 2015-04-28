import scala.collection.mutable.ListBuffer
/*calc_import*/

object Proofsearch{
	def derAllAux(loc:List[Locale], s:Sequent, rule:Rule) : List[(Rule, List[Sequent])] = {
		for (l <- loc){
			der(l, rule, s) match {
				case (Fail(), _) => ;
				case ret => return List(ret)
			}
		}
		return List()
	}

	def derAll(loc:List[Locale], s:Sequent) : List[(Rule, List[Sequent])] = ruleList.map(rule => derAllAux(loc, s, rule)).flatten

	def derAllM(loc:List[Locale], s:Sequent, macros : List[(String, Prooftree)] = List()) : List[(Rule, List[Sequent])] = 
		macros.map{ case (n, pt) => (RuleMacro(n.toList, replaceIntoPT(s, pt)), replaceIntoPT(s, pt)) }
			.filter{ case (r, pt) => isProofTreeWithCut(loc++collectPremisesToLocale(pt), pt) }
				.map{ case (r, pt) => (r, collectPremises(pt)) }

	def derTrees(loc:List[Locale], n:Int, seq:Sequent) : Option[Prooftree] = n match {
		case 0 => None
		case n => 
			for( (rule, derList) <- derAll(loc, seq).sortWith(_._2.length < _._2.length) ) {
				lazy val ders = derList.map(x => derTrees(loc, n-1, x))
				if(!ders.contains(None)){
					return Some(Prooftreea(seq, rule, ders.map{case Some(pt) => pt}))
				}
			}
			return None
	}

	def derTree(max:Int, loc:List[Locale], seq:Sequent, n:Int = 0) : Option[Prooftree] = {
		if (n > max) None
		else derTrees(loc, n, seq) match {
			case None => derTree(max, loc, seq, n+1)
			case res => res
		}
	}

	def main(args:Array[String]) {
/*	    Parser.parseSequent("a |- a >> a") match {
	    	case Some(res) => 

	    		derTree(5, List(Empty()), res, List()) match {
	    			case Some(r)=> println(r)
	    			case _ => println("not found")
	    		}

	    }

*/	    
	}


}

