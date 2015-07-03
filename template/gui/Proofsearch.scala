import scala.collection.mutable.ListBuffer
/*calc_import*/

object Proofsearch{

	val reversibleRules: List[Tuple2[Rule, Rule]] = {
		val rand : Sequent = Sequenta(Structure_Formula(Formula_Atprop(Atpropa(List('a')))),Structure_Formula(Formula_Atprop(Atpropa(List('a')))))

		val buf = ListBuffer[Tuple2[Rule, Rule]]()
		for (r <- ruleList) {
			val rl = rule(Premise(rand), r)
			val r_f = fst(rl)
			val r_s = snd(rl)(rand) getOrElse List[Rule]()
			if(r_s.length == 1) {
				ruleList.find( x => fst(rule(Premise(rand), x)) == r_s(0) ) match {
					case Some(res) => 
						val f_list = snd(rule(Premise(rand), res))(rand) getOrElse List[Rule]()
						if(f_list.length == 1) {
							if(r_f == f_list(0)) buf += Tuple2(r, res)
						}
					case None =>
				}
			}
		}

		// println(buf.toList)
		buf.toList
	}

	def restrictRules(rules : List[Rule], restr : List[Rule]) :  List[Rule] = {
		val buf = ListBuffer[Rule]()
		buf ++= rules
		for (r <- restr) {
			reversibleRules.find( x => r == x._1 ) match {
				case Some(r) => buf -= r._2
				case None =>  
			}
		}
		return buf.toList
	}

	def derAll(loc:List[Locale], s:Sequent, restr:List[Rule] = List(), useRules : List[Rule] = ruleList) : List[(Rule, List[Sequent])] = restrictRules(useRules, restr).map(rule => derAllAux(loc, s, rule)).flatten


	def derAllAux(loc:List[Locale], s:Sequent, rule:Rule) : List[(Rule, List[Sequent])] = {
		for (l <- loc){
			der(l, rule, s) match {
				case (Fail(), _) => ;
				case ret => return List(ret)
			}
		}
		return List()
	}


	// used for macro rules - manual only, not used for PS!!
	def derAllM(loc:List[Locale], s:Sequent, macros : List[(String, Prooftree)] = List()) : List[(Rule, List[Sequent])] = 
		macros.map{ case (n, pt) => (RuleMacro(n.toList, replaceIntoPT(s, pt)), replaceIntoPT(s, pt)) }
			.filter{ case (r, pt) => isProofTreeWithCut(loc++collectPremisesToLocale(pt), pt) }
				.map{ case (r, pt) => (r, collectPremises(pt)) }

	def derTrees(loc:List[Locale], n:Int, seq:Sequent, history:Rule = RuleZera(Id()), useRules : List[Rule] = ruleList) : Option[Prooftree] = n match {
		case 0 => None
		case n => 
			for( (rule, derList) <- derAll(loc, seq, List(history), useRules).sortWith(_._2.length < _._2.length) ) {
				lazy val ders = derList.map(x => derTrees(loc, n-1, x, rule))
				if(!ders.contains(None)){
					return Some(Prooftreea(seq, rule, ders.map{case Some(pt) => pt}))
				}
			}
			return None
	}

	def derTree(max:Int, loc:List[Locale], seq:Sequent, n:Int = 0, useRules : List[Rule] = ruleList) : Option[Prooftree] = {
		if (n > max) None
		else derTrees(loc=loc, n=n, seq=seq, useRules=useRules) match {
			case None => derTree(max, loc, seq, n+1, useRules)
			case res => res
		}
	}


}

