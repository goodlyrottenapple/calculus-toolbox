import swing.{Button, ListView, FileChooser, Publisher}
import swing.event.Event

import scala.collection.mutable.ListBuffer

import javax.swing.filechooser.FileNameExtensionFilter
import javax.swing.Icon

import java.io.PrintWriter

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants, TeXIcon}

/*calc_import*/
import PrintCalc.{sequentToString, prooftreeToString}

case class PTChanged(valid : Boolean) extends Event
case class MacroAdded() extends Event

case class CalcSession() extends Publisher {

	var relAKAMap : Map[Tuple2[Action, Agent], List[Action]] = Map()

	/*def relAKAOld(alpha : Action)(a : Agent)(beta: Action) : Boolean = (alpha, a, beta) match {
		// case (Actiona(List('e','p')), Agenta(List('c')), Actiona(List('e','w'))) => true
		// should we have this one as well? :
		// case (Actiona(List('e','w')), Agenta(List('c')), Actiona(List('e','p'))) => true
		case (Actiona(x), Agenta(a), Actiona(y)) => 
			if (x == y) true
			else {
				relAKAMap.get((Actiona(x), Agenta(a))) match {
					case Some(list) => list.indexOf(Actiona(y)) != -1
					case None => false
				}
			}
		case _ => false
	}*/

	def relAKA(alpha : Action)(a : Agent) : List[Action] = relAKAMap.get((alpha, a)) match {
		case Some(h::list) =>
		// makes sure relAKA(a, x, a) is always true
		if(alpha != h && list.indexOf(alpha) == -1) alpha::h::list
		else h::list
		case None => List(alpha)
	}

	var currentSequent : Sequent = Sequenta(Structure_Formula(Formula_Atprop(Atpropa(List('a')))),Structure_Formula(Formula_Atprop(Atpropa(List('a')))))

	private var _currentPT : Prooftree = Prooftreea( Sequenta(Structure_Formula(Formula_Atprop(Atpropa(List('a')))),Structure_Formula(Formula_Atprop(Atpropa(List('a'))))), RuleZera(Id()), List())
	
	def currentPT = _currentPT
	def currentPT_= (value:Prooftree):Unit = {
		_currentPT = value
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	var currentPTsel : Int = -1

	val assmsBuffer = ListBuffer[(Icon, Sequent)]()
	val ptBuffer = ListBuffer[(Icon, Prooftree)]()

	val macroBuffer = ListBuffer[(String, Prooftree)]()


	val listView = new ListView[(Icon, Sequent)]() {
		//maximumSize = new java.awt.Dimension(200, 300)
    	listData = assmsBuffer
    	renderer = ListView.Renderer(_._1)
  	}
  	val ptListView = new ListView[(Icon, Prooftree)]() {  
  		//maximumSize = new java.awt.Dimension(200, 300) 
    	listData = ptBuffer
    	renderer = ListView.Renderer(_._1)
    }

    val macroListView = new ListView[(String, Prooftree)]() {  
  		//maximumSize = new java.awt.Dimension(200, 300) 
    	listData = macroBuffer
    	renderer = ListView.Renderer(_._1)
    }

    def currentLocale() : List[Locale] = List(
		Empty(), 
		RelAKA(relAKA)//, 
		//Swapout(relAKA, List(Actiona(List('e','p','a'))) )
	) ++ assmsBuffer.toList.map({case (i,s) => Premise(s)})



    var proofDepth = 5
	/*val addAssmButton = new Button {
		text = "Add assm"
	}
	val removeAssmButton = new Button {
		text = "Remove assm"
		enabled = false
	}

	val addPtButton = new Button {
		text = "Add PT"
		visible = false
	}
	val loadPTButton = new Button {
		text = "Load PT"
		enabled = false
	}
	val removePTsButton = new Button {
		text = "Remove PTs"
		enabled = false
	}*/

    def addAssm(seq:Sequent = currentSequent) = {
		val formula = new TeXFormula(sequentToString(seq))
		val newAssm = (formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, 15), seq)

		assmsBuffer.find(_._2 ==seq) match {
			case Some(r) => 
			case None => 
				assmsBuffer += newAssm
				listView.listData = assmsBuffer
				//if (!removeAssmButton.enabled) removeAssmButton.enabled = true
		}
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}
	def removeAssms() = {
		for (i <- listView.selection.items) assmsBuffer -= i
		listView.listData = assmsBuffer
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	def clearAssms() = {
		assmsBuffer.clear()
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

    def addPT(pt: Prooftree = currentPT) = {
		val newPt = (ptToIcon(pt), pt)
		ptBuffer += newPt
		ptListView.listData = ptBuffer
		currentPTsel = ptBuffer.indexOf(newPt)

		//if (!removePTsButton.enabled) removePTsButton.enabled = true
		//if (!loadPTButton.enabled) loadPTButton.enabled = true
	}

	def savePT(ptSel: Int = currentPTsel, pt : Prooftree = currentPT) = {
		if (ptSel >= 0) {
			println("Saving")
			val sel : (Icon, Prooftree) = ptBuffer(ptSel)
			// if delete or add below was used, we want a new pt....
			if (concl(sel._2) == concl(pt)){
				val newPt = (sel._1, pt)
				ptBuffer.update(ptSel, newPt)
				ptListView.listData = ptBuffer
			} else {
				addPT(pt)
			}
		} else addPT(pt)
		//if (!removePTsButton.enabled) removePTsButton.enabled = true
		//if (!loadPTButton.enabled) loadPTButton.enabled = true
	}

	def loadPT() = {
		var sel = ptListView.selection.items.head
		currentPTsel = ptBuffer.indexOf(sel)
		currentPT = sel._2
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	def removePTs() = {
		val current = ptBuffer(currentPTsel)
		for (i <- ptListView.selection.items) {
			ptBuffer -= i
		}
		ptListView.listData = ptBuffer
		currentPTsel = ptBuffer.indexOf(current)
		/*if (ptListView.listData.isEmpty){
			removePTsButton.enabled = false
			loadPTButton.enabled = false
		}*/
	}

	def clearPT() = {
		ptBuffer.clear()
		currentPTsel = -1
		ptListView.listData = ptBuffer
	}

	def addAssmFromSelPT() : Unit = {
		var sel = ptListView.selection.items.head
		addAssm(concl(sel._2))
	}

	def exportLatexFromSelPT() : Unit = {
		var sel = ptListView.selection.items.head

		val chooser = new FileChooser(new java.io.File(".")) {
			title = "Save LaTeX File"
			fileFilter = new FileNameExtensionFilter("LaTeX (.tex)", "tex")
		}
		val result = chooser.showSaveDialog(null)
		if (result == FileChooser.Result.Approve) {
			val file = if (!chooser.selectedFile.toString.endsWith(".tex")) chooser.selectedFile.toString+".tex" else chooser.selectedFile.toString
			Some(new PrintWriter(file)).foreach{p =>
		    	p.write(prooftreeToString(sel._2) + "\\DisplayProof")
		    	p.close
		    }
		}

	}

	def rulifyPT() : Unit = {
		var sel = ptListView.selection.items.head
		val ptMacro = rulifyProoftree(sel._2)
		new MacroAddDialog(pt=ptMacro).rule match {
			case Some(str) => 
				if(str != ""){
					println(str)
					macroBuffer += Tuple2(str, ptMacro)

					println("Conclusion: "+sequentToString(concl(ptMacro), PrintCalc.ASCII))

					for (c <- collectPremises(ptMacro)){
						println("Prem: "+sequentToString(c, PrintCalc.ASCII))

					}
					macroListView.listData = macroBuffer

					//publish(MacroAdded())
				}
			case _ => println("cancel")
		}
		//val pt = rulifyProoftree(sel._2)
		//addPT(pt)
	}

	def ptToIcon(pt:Prooftree) : TeXIcon = {
		new TeXFormula(sequentToString(concl(pt))).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
	}

	def findMatches(seq: Sequent) : List[Prooftree] = for {
		(i, pt) <- ptBuffer.toList
		if concl(pt) == seq
	} yield pt

	def findMatchesMacro(seq: Sequent) : List[Prooftree] = for {
		(i, pt) <- ptBuffer.toList
		if replaceAll(match_Sequent(concl(pt), seq), concl(pt)) == seq
	} yield pt

	def mergePTs(repPt: Prooftree, insertPoint:SequentInPt, root:SequentInPt, children: SequentInPt => Iterable[SequentInPt]) : Prooftree = {
	    if(insertPoint == root) return repPt
	    return Prooftreea( root.seq, root.rule, children(root).toList.map(x => mergePTs(repPt, insertPoint, x, children)) )
	}

	def deleteAbove(deletePoint:SequentInPt, root:SequentInPt, children: SequentInPt => Iterable[SequentInPt]) : Prooftree = {
	    if(deletePoint == root) return Prooftreea(root.seq, RuleZera(Prem()), List())
	    return Prooftreea( root.seq, root.rule, children(root).toList.map( x => deleteAbove(deletePoint, x, children) ) )
	}

	def rebuildFromPoint(root:SequentInPt, children: SequentInPt => Iterable[SequentInPt]) : Prooftree = 
		return Prooftreea( root.seq, root.rule, children(root).toList.map( x => rebuildFromPoint(x, children) ) )

}