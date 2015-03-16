import swing.{Action, Component, Dialog, Swing, MenuItem, Graphics2D, ListView}
import swing.event.{ButtonClicked, MouseClicked}

import javax.swing.KeyStroke.getKeyStroke
import java.awt.event.KeyEvent
import java.awt.Color
import java.awt.geom.Rectangle2D

import scala.collection.JavaConversions._

import org.abego.treelayout.TreeLayout
import org.abego.treelayout.util.{DefaultConfiguration, DefaultTreeForTreeLayout}

/*calc_import*/
import PrintCalc.sequentToString
import Proofsearch._

class ProofTreePanel(session : CalcSession, gapBetweenLevels:Int = 10, gapBetweenNodes:Int = 60) extends scala.swing.Panel {
	val configuration = new DefaultConfiguration[SequentInPt](gapBetweenLevels, gapBetweenNodes, org.abego.treelayout.Configuration.Location.Bottom)
	val nodeExtentProvider = new SequentInPtNodeExtentProvider()

	// create the layout
	var treeLayout = new TreeLayout[SequentInPt](createPTree(session.currentPT), nodeExtentProvider, configuration)

	val OFFSET_X = 20
	val OFFSET_Y = 20

	peer.setLayout(null)
	border = Swing.EmptyBorder(10, 10, 10, 10)

	var selectedSequentInPt : Option[SequentInPt] = None
	var edit = false

	preferredSize = treeLayout.getBounds().getBounds().getSize()

	def tree = treeLayout.getTree()

	def children(parent:SequentInPt) : Iterable[SequentInPt] = tree.getChildren(parent)

	def boundsOfNode(node:SequentInPt) : Rectangle2D.Double = treeLayout.getNodeBounds().get(node)

	def createPTreeAux(proof: Prooftree, tree: DefaultTreeForTreeLayout[SequentInPt], root:SequentInPt, size:Int=20 ) : Unit = proof match {
		case Zer(seq, r) => tree.addChild(root, new SequentInPt(seq, RuleZera(r), size))
    	case Unary(seq, r, pt) => {
    		val l = new SequentInPt(seq, RuleUa(r), size)
    		tree.addChild(root, l)
    		createPTreeAux(pt, tree, l)
    	}
       	case Display(seq, r, pt) => {
    		val l = new SequentInPt(seq, RuleDispa(r), size)
    		tree.addChild(root, l)
    		createPTreeAux(pt, tree, l)
    	}
    	case Operational(seq, r, pt) => {
    		val l = new SequentInPt(seq, RuleOpa(r), size)
    		tree.addChild(root, l)
    		createPTreeAux(pt, tree, l)
    	}
    	case Binary(seq, r, pt1, pt2) => {
    		val l = new SequentInPt(seq, RuleBina(r), size)
    		tree.addChild(root, l)
    		createPTreeAux(pt1, tree, l)
    		createPTreeAux(pt2, tree, l)
    	}
    	case Cut(seq, form, pt1, pt2) => {
    		val l = new SequentInPt(seq, RuleCuta(SingleCut()), size, Some(form))
    		tree.addChild(root, l)
    		createPTreeAux(pt1, tree, l)
    		createPTreeAux(pt2, tree, l)
    	}
	}

	def createPTree(proof: Prooftree, size:Int=20) : DefaultTreeForTreeLayout[SequentInPt] = proof match {
		case Zer(seq, r) => new DefaultTreeForTreeLayout[SequentInPt]( new SequentInPt(seq, RuleZera(r), size) )
    	case Unary(seq, r, pt) => {
    		val l = new SequentInPt(seq, RuleUa(r), size)
    		val tree = new DefaultTreeForTreeLayout[SequentInPt](l)
    		createPTreeAux(pt, tree, l, size)
    		return tree
    	}
       	case Display(seq, r, pt) => {
    		val l = new SequentInPt(seq, RuleDispa(r), size)
    		val tree = new DefaultTreeForTreeLayout[SequentInPt](l)
    		createPTreeAux(pt, tree, l, size)
    		return tree
    	}
    	case Operational(seq, r, pt) => {
    		val l = new SequentInPt(seq, RuleOpa(r), size)
    		val tree = new DefaultTreeForTreeLayout[SequentInPt](l)
    		createPTreeAux(pt, tree, l, size)
    		return tree
    	}
    	case Binary(seq, r, pt1, pt2) => {
    		val l = new SequentInPt(seq, RuleBina(r), size)
    		val tree = new DefaultTreeForTreeLayout[SequentInPt](l)
    		createPTreeAux(pt1, tree, l, size)
    		createPTreeAux(pt2, tree, l, size)
    		return tree
    	}
    	case Cut(seq, form, pt1, pt2) => {
    		val l = new SequentInPt(seq, RuleCuta(SingleCut()), size, Some(form))
    		val tree = new DefaultTreeForTreeLayout[SequentInPt](l)
    		createPTreeAux(pt1, tree, l, size)
    		createPTreeAux(pt2, tree, l, size)
    		return tree
    	}
	}


	protected def add(comp: Component, x: Int, y: Int): Unit = {
		val p = comp.peer
		p.setLocation(x+OFFSET_X, y+OFFSET_Y)
		p.setSize(p.getPreferredSize)
		peer.add(p)
		listenTo(comp)
	}

	listenTo(mouse.clicks)
	reactions += {
		case ButtonClicked(b) if( edit ) =>

			val pressed = b.asInstanceOf[SequentInPt]
			/*println(b.text)
			println("Children:")
			for (child <- children(pressed)) { 
				println(child.text)
			}*/
			unselect()
			selectedSequentInPt = Some(pressed)
			pressed.border = Swing.LineBorder(Color.black)
			pressed.sel = true
			//val b1 = boundsOfNode(pressed)
			popup.peer.show(b.peer, OFFSET_X, OFFSET_Y)

		case m : MouseClicked => 
			selectedSequentInPt = None
			unselect()

	}

	

	val popup = new PopupMenu
	val addAssm = new MenuItem(Action("Add as assm") {
		selectedSequentInPt match {
			case Some(seqIPT) => session.addAssm(seqIPT.seq)
		}
		
	})
	popup.add(addAssm);

	val merge = new MenuItem(Action("Merge") {
		selectedSequentInPt match {
			case Some(selSeq) =>
				session.findMatches(selSeq.seq) match {
					case List() => 
						Dialog.showMessage(null, "No matching pt found!", "Error")
					case (x::xs) => 
						session.currentPT = session.mergePTs(x, selSeq, tree.getRoot(), children)
            			update()
            			//session.addPT()
				}
				
		}
		
	})
	popup.add(merge);

	val findPT = new MenuItem(new Action("FindPT") {
		accelerator = Some(getKeyStroke('f'))
      	def apply = {
			selectedSequentInPt match {
				case Some(selSeq) =>
					tree.isLeaf(selSeq) match {
						case true =>
							derTree(5, selSeq.seq) match {
	              				case Some(r) => 
	              					session.currentPT = session.mergePTs(r, selSeq, tree.getRoot(), children)
	            					update()
	            				case None =>
	            					Dialog.showMessage(null, "PT couldn't be found", "Error")
	            			}
						case false => Dialog.showMessage(null, "Sequent not a premise", "Error")
					}
					
			}
		}
	})
	popup.add(findPT);


	def addAbove() = {
		selectedSequentInPt match {
			case Some(selSeq) =>
				if(tree.isLeaf(selSeq)) {
					new SequentInputDialog().sequent match {
						case Some(s) =>
							//println(selSeq.seq)
							//println(derAll(selSeq.seq).filter{ case (r,l) => l.exists(_ == s)})
							val pair = derAll(selSeq.seq).filter{ case (r,l) => l.exists(_ == s)} match {
								case List() => None
								case List((rule, derList)) => Some(rule, derList)
								case list => new RuleSelectDialog(list=list).pair 
							}

							pair match {
								case None => Dialog.showMessage(null, "No rule found for the given sequent", "Error")
								case Some((rule, derList)) =>
									val pt = rule match {
										case RuleZera(r) => Zer(derList(0), r)
										case RuleUa(r) => Unary( selSeq.seq, r, Zer(derList(0), Prem()) )
										case RuleDispa(r) => Display( selSeq.seq, r, Zer(derList(0), Prem()) )
										case RuleOpa(r) => Operational( selSeq.seq, r, Zer(derList(0), Prem()) )
										case RuleBina(r) => Binary( selSeq.seq, r, Zer(derList(0), Prem()), Zer(derList(1), Prem()) )
										case _ => Zer(derList(0), Prem())
									}
									session.currentPT = session.mergePTs(pt, selSeq, tree.getRoot(), children)
									update()
							}
						case None => Dialog.showMessage(null, "Invalid sequent entered", "Error")
					}
				} 
				else Dialog.showMessage(null, "The sequent is not a leaf please delete pt above to proceed", "Error")
		}
	}

	val add1 = new MenuItem(new Action("Add above") {
		accelerator = Some(getKeyStroke('a'))
      	def apply = addAbove()
	})
	popup.add(add1);

	def addBelow() = {
		selectedSequentInPt match {
			case Some(selSeq) =>
				if(tree.getRoot() == selSeq) {
					new SequentInputDialog().sequent match {
						case Some(s) =>
							//println(selSeq.seq)
							//println(derAll(selSeq.seq).filter{ case (r,l) => l.exists(_ == s)})
							val pair = derAll(s).filter{ case (r,l) => l.exists(_ == selSeq.seq)} match {
								case List() => None
								case List((rule, derList)) => Some(rule, derList)
								case list => new RuleSelectDialog(list=list).pair 
							}

							pair match {
								case None => Dialog.showMessage(null, "No rule found for the given sequent", "Error")
								case Some((rule, derList)) =>
									val rest = session.rebuildFromPoint(selSeq, children)
									session.currentPT = rule match {
										case RuleZera(r) => Zer(s, r)
										case RuleUa(r) => Unary( s, r, rest )
										case RuleDispa(r) => Display( s, r, rest )
										case RuleOpa(r) => Operational( s, r, rest )
										case RuleBina(r) => 
											if(concl(rest) == derList(0)) Binary( s, r, rest, Zer(derList(1), Prem()) )
											else Binary( s, r, rest, Zer(derList(0), Prem()) )
										case _ => Zer(s, Prem())
									}
									update()
							}
						case None => Dialog.showMessage(null, "Invalid sequent entered", "Error")
					}
				} 
				else Dialog.showMessage(null, "The sequent is not a leaf please delete pt above to proceed", "Error")
		}
	}


	val add2 = new MenuItem(new Action("Add below") {
		accelerator = Some(getKeyStroke('A'))
      	def apply = addBelow()		
	})
	popup.add(add2);

	val delete1 = new MenuItem(new Action("Delete above") {
		accelerator = Some(getKeyStroke('d'))
      	def apply = {
			selectedSequentInPt match {
				case Some(selSeq) =>
					session.currentPT = session.deleteAbove(selSeq, tree.getRoot(), children)
	            	update()
			}
		}
	})
	popup.add(delete1);

	val delete2 = new MenuItem(new Action("Delete below") {
		accelerator = Some(getKeyStroke('D'))
      	def apply = {
      		selectedSequentInPt match {
				case Some(selSeq) =>
					session.currentPT = session.rebuildFromPoint(selSeq, children)
	            	update()
					
			}
		}
	})
	popup.add(delete2);


	def unselect(root:SequentInPt = tree.getRoot) : Unit = {
		root.border = Swing.EmptyBorder(0,0,0,0)
		for (child <- children(root)) {
			child.border = Swing.EmptyBorder(0,0,0,0)
			child.sel = false
			unselect(child)
		}

	}

	def update() = {
		peer.removeAll()
		treeLayout = new TreeLayout[SequentInPt](createPTree(session.currentPT), nodeExtentProvider, configuration)
		build()
		peer.revalidate()
		peer.repaint()
	}

	def build() = {
		for (sequentInPt <- treeLayout.getNodeBounds().keySet()) {
			val box = boundsOfNode(sequentInPt)
			add(sequentInPt, (box.x).toInt, (box.y).toInt)
		}
	}

	def paintEdges(g:Graphics2D, parent:SequentInPt) : Unit = {
		val b1 = boundsOfNode(parent)
		val y = (b1.getMinY()).toInt-3
		var xmin = (b1.getMinX()).toInt
		var xmax = (b1.getMaxX()).toInt //+15


		for (child <- children(parent)) { 
			val b2 = boundsOfNode(child)
			if( (b2.getMinX()).toInt < xmin) xmin = (b2.getMinX()).toInt
			if( (b2.getMaxX()).toInt > xmax) xmax = (b2.getMaxX()).toInt

			paintEdges(g, child)
		}

		//g.drawLine( xmin, y, xmax+15, y )
		g.drawLine( xmin+OFFSET_X, y+OFFSET_Y, xmax+OFFSET_X, y+OFFSET_Y )
		parent.ruleIcon.paintIcon(null, g, xmax+5+OFFSET_X, y-(parent.ruleIcon.getIconHeight/2)+OFFSET_Y)
		//g.drawString(parent.strule, xmax+5+OFFSET_X, y+5+OFFSET_Y)
	}

	override def paintComponent(g: Graphics2D) = {
		super.paintComponent(g)
		paintEdges(g, tree.getRoot())
    }
}

class SequentInPtNodeExtentProvider extends org.abego.treelayout.NodeExtentProvider[SequentInPt] {
	def getWidth(treeNode:SequentInPt) = treeNode.width
	def getHeight(treeNode:SequentInPt) = treeNode.height
}