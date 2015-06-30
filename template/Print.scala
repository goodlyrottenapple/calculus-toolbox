/*calc_import*/

object PrintCalc{
	val ASCII = "ascii"
	val LATEX = "latex"
	val ISABELLE = "isabelle"


	def bracketIf(in:String, b: Boolean = true) : String = {
		if(b) return "(" + in + ")"
		else return in
	}

	def stringToString(x:List[Char], format:String = LATEX) : String = format match {
		case ASCII => x.mkString
		case LATEX => x.mkString
		case ISABELLE => "''" + x.mkString +"''"
	}

/*/*uncommentL?Structure*/
	def structure_listToString(in:List[Structure], format:String = LATEX) : String = "[" + in.map(x => structureToString(x, format)).mkString(", ") + "]" 
/*uncommentR?Structure*/*/

/*print_calc_structure*/

/*print_calc_structure_rules*/

/*/*uncommentL?core_compiled*/
	def rulemacroToString(a : List[Char], pt : Prooftree, format : String = LATEX) : String = format match { 
		case ASCII => "Macro " + stringToString(a, format) + prooftreeToString(pt, format)
		case ISABELLE => "(RuleMacro " + stringToString(a, format) + prooftreeToString(pt, format) + ")"
		case LATEX => "Macro/" + stringToString(a, format)
	}

	def sequentToLatexString(seq:Sequent) = sequentToString(seq, LATEX)

	def prooftreeListToString(in:List[Prooftree], format:String = LATEX, sequentLatexPrint: Sequent => String = sequentToLatexString) : String = format match {
		case ASCII | ISABELLE => "[" + in.map(x => prooftreeToString(x, format, sequentLatexPrint)).mkString(", ") + "]"
		case LATEX => in.map(x => prooftreeToString(x, format, sequentLatexPrint)).mkString("\n")
	}


	def prooftreeToString(in:Prooftree, format:String = LATEX, sequentLatexPrint: Sequent => String = sequentToLatexString) : String = format match {
		case ASCII =>
			in match {
				case Prooftreea(a,b,c) => "(" + sequentToString(a, format) + " " + "<==" + " (" + ruleToString(b, format) + ") " + prooftreeListToString(c, format, sequentLatexPrint) + ")"
			}
		case LATEX =>
			in match {
				case Prooftreea(a,b,List()) => "\\RightLabel{ $" + ruleToString(b) + "$ }\n\\AxiomC{$ " + sequentLatexPrint(a)  + " $}"
				case Prooftreea(a,b,List(c)) => prooftreeToString(c, format, sequentLatexPrint) + "\\RightLabel{ $" + ruleToString(b) + "$ }\n\\UnaryInfC{$ " + sequentLatexPrint(a)  + " $}"
				case Prooftreea(a,b,List(c, d)) => prooftreeListToString(List(c, d), format, sequentLatexPrint) + "\\RightLabel{ $" + ruleToString(b) + "$ }\n\\BinaryInfC{$ " + sequentLatexPrint(a)  + " $}"
				case Prooftreea(a,b,List(c, d, e)) => prooftreeListToString(List(c, d, e), format, sequentLatexPrint) + "\\TrinaryInfC{$ " + sequentLatexPrint(a)  + " $}\n"
				case Prooftreea(a,b,List(c, d, e, f)) => prooftreeListToString(List(c, d, e, f), format, sequentLatexPrint) + "\\QuaternaryInfC{$ " + sequentLatexPrint(a)  + " $}\n"
				case Prooftreea(a,b,list) => prooftreeListToString(list, format, sequentLatexPrint) + "\\QuinaryInfC{$ " + sequentLatexPrint(a)  + " $}\n"
			}
		case ISABELLE =>
			in match {
				case Prooftreea(a,b,c) => "(" + sequentToString(a, format) + " " + "\\<Longleftarrow>" + " " + "PT" + " " + ruleToString(b, format) + " " + prooftreeListToString(c, format, sequentLatexPrint) + ")"
			}
	}
	
	/*def printCalcDef() : String = {
		val buf_Zer = scala.collection.mutable.ListBuffer.empty[String]
		val buf_U = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Op = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Disp = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Bin = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Cut = scala.collection.mutable.ListBuffer.empty[String]

		for (r <- ruleList) {

			val loc = List(RelAKA((x => y => z => true)))
			val ret = prooftreeToString(Prooftreea(fst(rule(loc, r)), r, snd(rule(loc, r))))
			// val ant = fst(rule(r))
			// val cons = snd(rule(r))
			// ret ++= "$" + ruleToString(r) + "$\n"
			// if(cons.length == 1){
			// 	ret ++= "\\AxiomC{$ " + sequentToString(cons(0), LATEX) + " $}\n"
			// 	ret ++= "\\UnaryInfC{$ " + sequentToString(ant, LATEX) + " $}\n"
			// }
			// else if(cons.length == 2){
			// 	ret ++= "\\AxiomC{$ " + sequentToString(cons(0), LATEX) + " $}\n"
			// 	ret ++= "\\AxiomC{$ " + sequentToString(cons(1), LATEX) + " $}\n"
			// 	ret ++= "\\BinaryInfC{$ " + sequentToString(ant, LATEX) + " $}\n"
			// }
			// else{
			// 	ret ++= "\\AxiomC{$ " + sequentToString(ant, LATEX) + " $}\n"
			// }
			// ret ++= "\n\\end{prooftree}"
			buf_Zer += ret
			// r match {
		 //        case RuleBina(a) => buf_Bin += ret.toString
		 //        case RuleCuta(a) => buf_Cut += ret.toString
		 //        case RuleDispa(a) => buf_Disp += ret.toString
		 //        case RuleOpa(a) => buf_Op += ret.toString
		 //        case RuleUa(a) => buf_U += ret.toString
		 //        case RuleZera(a) => buf_Zer += ret.toString
			// }
		}
		return "\\subsection{Zer Rules}\n" + buf_Zer.toList.mkString("\n") /*+
				"\\subsection{Unary Rules}\n" + buf_U.toList.mkString("\n") +
				"\\subsection{Display Rules}\n" + buf_Disp.toList.mkString("\n") +
				"\\subsection{Operational Rules}\n" + buf_Op.toList.mkString("\n") +
				"\\subsection{Binary Rules}\n" + buf_Bin.toList.mkString("\n") +
				"\\subsection{Cut Rules}\n" + buf_Cut.toList.mkString("\n")*/

	}
*/
/*uncommentR?core_compiled*/*/
}
