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

	def cr[A](xs: List[A], zss: List[List[A]]): List[List[A]] = {
	    for {
	        x <- xs
	        zs <- zss
	    } yield {
	        x :: zs
	    }
	}
	def zss[A]: List[List[A]] = List(List())

	def crossProd[A](inputList : List[List[A]]) : List[List[A]] = inputList.foldRight( zss[A] ) (cr _)

	def derTrees(loc:List[Locale], n:Int, seq:Sequent) : List[Prooftree] = n match {
		case 0 => List[Prooftree]()
		case n => 
			var ret = new ListBuffer[Prooftree]()
			for( (rule, derList) <- derAll(loc, seq).sortWith(_._2.length < _._2.length) ) {
				lazy val ders = crossProd( derList.map(x => derTrees(loc, n-1, x)) )

				for(possibleDer <- ders ) {
					ret += Prooftreea(seq, rule, possibleDer)
				}
			}
			return ret.toList
	}

	def derTree(max:Int, loc:List[Locale], seq:Sequent, n:Int = 0) : Option[Prooftree] = {
		if (n > max) None
		else derTrees(loc, n, seq) match {
			case Nil => derTree(max, loc, seq, n+1)
			case res => Some(res(0))
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

