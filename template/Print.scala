/*calc_import*/

object PrintCalc{
	val ASCII = "ascii"
	val LATEX = "latex"
	val ISABELLE = "isabelle"

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
	def prooftreeListToString(in:List[Prooftree], format:String = LATEX) : String = "[" + in.map(x => prooftreeToString(x, format)).mkString(", ") + "]" 
	// add print pt!!!!
	def prooftreeToString(in:Prooftree, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Prooftreea(a,b,c) => "(" + sequentToString(a, format) + " " + "<==" + " " + ruleToString(b, format) + " " + prooftreeListToString(c, format) + ")"
			}
		case LATEX =>
			in match {
				case Prooftreea(a,b,c) => "\\AxiomC{$ " + sequentToString(a, format) + prooftreeListToString(c, format) + " $}\n"
			}
		case ISABELLE =>
			in match {
				case Prooftreea(a,b,c) => "(" + sequentToString(a, format) + " " + "\\<Longleftarrow>" + " " + "PT" + " " + ruleToString(b, format) + " " + prooftreeListToString(c, format) + ")"
			}
	}
	
/*	def printCalcDef() : String = {

		val buf_Zer = scala.collection.mutable.ListBuffer.empty[String]
		val buf_U = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Op = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Disp = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Bin = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Cut = scala.collection.mutable.ListBuffer.empty[String]

		for (r <- ruleList) {
			val ret = new StringBuilder("\\begin{prooftree}\n")

			val ant = fst(rule(r))
			val cons = snd(rule(r))
			ret ++= "$" + ruleToString(r) + "$\n"
			if(cons.length == 1){
				ret ++= "\\AxiomC{$ " + sequentToString(cons(0), LATEX) + " $}\n"
				ret ++= "\\UnaryInfC{$ " + sequentToString(ant, LATEX) + " $}\n"
			}
			else if(cons.length == 2){
				ret ++= "\\AxiomC{$ " + sequentToString(cons(0), LATEX) + " $}\n"
				ret ++= "\\AxiomC{$ " + sequentToString(cons(1), LATEX) + " $}\n"
				ret ++= "\\BinaryInfC{$ " + sequentToString(ant, LATEX) + " $}\n"
			}
			else{
				ret ++= "\\AxiomC{$ " + sequentToString(ant, LATEX) + " $}\n"
			}
			ret ++= "\n\\end{prooftree}"

			r match {
		        case RuleBina(a) => buf_Bin += ret.toString
		        case RuleCuta(a) => buf_Cut += ret.toString
		        case RuleDispa(a) => buf_Disp += ret.toString
		        case RuleOpa(a) => buf_Op += ret.toString
		        case RuleUa(a) => buf_U += ret.toString
		        case RuleZera(a) => buf_Zer += ret.toString
			}
		}
		return "\\subsection{Zer Rules}\n" + buf_Zer.toList.mkString("\n") +
				"\\subsection{Unary Rules}\n" + buf_U.toList.mkString("\n") +
				"\\subsection{Display Rules}\n" + buf_Disp.toList.mkString("\n") +
				"\\subsection{Operational Rules}\n" + buf_Op.toList.mkString("\n") +
				"\\subsection{Binary Rules}\n" + buf_Bin.toList.mkString("\n") +
				"\\subsection{Cut Rules}\n" + buf_Cut.toList.mkString("\n")

	}
*/
/*uncommentR?core_compiled*/*/
}
