import swing.{Button, ListView}
import scala.collection.mutable.ListBuffer

import javax.swing.Icon

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants, TeXIcon}

/*calc_import*/
import PrintCalc.sequentToString

case class CalcSession() {
	var currentSequent : Sequent = Sequenta(Structure_Formula(Formula_Atprop(Atpropa(List('a')))),Structure_Formula(Formula_Atprop(Atpropa(List('a')))))
	var currentPT : Prooftree = Prooftreea( Sequenta(Structure_Formula(Formula_Atprop(Atpropa(List('a')))),Structure_Formula(Formula_Atprop(Atpropa(List('a'))))), RuleZera(Id()), List())
	var currentLocale : List[Locale] = List(Empty())

	val assmsBuffer = ListBuffer[(Icon, Sequent)]()
	val ptBuffer = ListBuffer[(Icon, Prooftree)]()

	val listView = new ListView[(Icon, Sequent)]() {   
    	listData = assmsBuffer
    	renderer = ListView.Renderer(_._1)
  	}
  	val ptListView = new ListView[(Icon, Prooftree)]() {   
    	listData = ptBuffer
    	renderer = ListView.Renderer(_._1)
    }

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
	}
	def removeAssms() = {
		for (i <- listView.selection.items) assmsBuffer -= i
		listView.listData = assmsBuffer
		//if (listView.listData.isEmpty) removeAssmButton.enabled = false
	}

	def clearAssms() = {
		assmsBuffer.clear()
	}

    def addPT(pt: Prooftree = currentPT) = {
		val newPt = (ptToIcon(pt), pt)
		ptBuffer += newPt
		ptListView.listData = ptBuffer
		//if (!removePTsButton.enabled) removePTsButton.enabled = true
		//if (!loadPTButton.enabled) loadPTButton.enabled = true
	}
	def loadPT() = {
		var sel = ptListView.selection.items.head
		currentPT = sel._2
	}
	def removePTs() = {
		for (i <- ptListView.selection.items) ptBuffer -= i
		ptListView.listData = ptBuffer
		/*if (ptListView.listData.isEmpty){
			removePTsButton.enabled = false
			loadPTButton.enabled = false
		}*/
	}

	def clearPT() = {
		ptBuffer.clear()
	}

	 def addAssmFromSelPT() : Unit = {
		var sel = ptListView.selection.items.head
		addAssm(concl(sel._2))
	}

	def ptToIcon(pt:Prooftree) : TeXIcon = {
		new TeXFormula(sequentToString(concl(pt))).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
	}

	def findMatches(seq: Sequent) : List[Prooftree] = for {
		(i, pt) <- ptBuffer.toList
		if concl(pt) == seq
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