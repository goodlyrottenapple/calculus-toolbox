import swing.{Action, Component, Dialog, Swing, MenuItem, Graphics2D, ListView}
import swing.event.{ButtonClicked, MouseClicked}

import javax.swing.KeyStroke.getKeyStroke
import java.awt.event.KeyEvent
import java.awt.Color
import java.awt.Dimension

import java.awt.geom.Rectangle2D

import java.awt.Toolkit;
import java.awt.datatransfer.Clipboard;
import java.awt.datatransfer.StringSelection;


import scala.collection.JavaConversions._

import org.abego.treelayout.TreeLayout
import org.abego.treelayout.util.{DefaultConfiguration, DefaultTreeForTreeLayout}

/*calc_import*/
import PrintCalc.sequentToString
import Proofsearch._


class ProofTreePanel(session : CalcSession, gapBetweenLevels:Int = 10, gapBetweenNodes:Int = 80, editable : Boolean = true) extends scala.swing.Panel {
	val configuration = new DefaultConfiguration[SequentInPt](gapBetweenLevels, gapBetweenNodes, org.abego.treelayout.Configuration.Location.Bottom)
	val nodeExtentProvider = new SequentInPtNodeExtentProvider()

	// create the layout
	//println("abbrevMAP:")
	//println(session.abbrevMap.toMap)
	var treeLayout = new TreeLayout[SequentInPt](createPTree(session.currentPT), nodeExtentProvider, configuration)

	val OFFSET_X = 20
	val OFFSET_Y = 20

	peer.setLayout(null)
	border = Swing.EmptyBorder(10, 10, 10, 10)

	var selectedSequentInPt : Option[SequentInPt] = None

	preferredSize = new Dimension(treeLayout.getBounds().getBounds().getSize().width+2*OFFSET_X, treeLayout.getBounds().getBounds().getSize().height+2*OFFSET_Y)

	var seqTreeViewDialog : Option[SequentTreeViewDialog] = None//new SequentTreeViewDialog(null, concl(session.currentPT))

	def tree = treeLayout.getTree()

	def children(parent:SequentInPt) : Iterable[SequentInPt] = tree.getChildren(parent)

	def boundsOfNode(node:SequentInPt) : Rectangle2D.Double = treeLayout.getNodeBounds().get(node)

	def createPTreeAux(proof: Prooftree, tree: DefaultTreeForTreeLayout[SequentInPt], root:SequentInPt, size:Int=20) : Unit = proof match {
		case Prooftreea(seq, r, list) => {
    		val l = new SequentInPt(seq, r, size, None, session)
    		tree.addChild(root, l)
    		list.foreach( x => createPTreeAux(x, tree, l, size) )
    	}
	}

	def createPTree(proof: Prooftree, size:Int=20)  : DefaultTreeForTreeLayout[SequentInPt] = proof match {
		case Prooftreea(seq, r, list) => {
    		val l = new SequentInPt(seq, r, size, None, session)
    		val tree = new DefaultTreeForTreeLayout[SequentInPt](l)
    		list.foreach( x => createPTreeAux(x, tree, l) )
    		return tree
    	}
	}


	protected def add(comp: SequentInPt, x: Int, y: Int): Unit = {
		val p = comp.peer
		p.setLocation(x+OFFSET_X, y+OFFSET_Y)
		//comp.ruleButton.peer.setLocation(x+p.getPreferredSize.width+OFFSET_X, y+OFFSET_Y-p.getPreferredSize.height/2)
		comp.ruleButton.peer.setSize(comp.ruleButton.peer.getPreferredSize)
		p.setSize(p.getPreferredSize)
		peer.add(p)
		peer.add(comp.ruleButton.peer)


//parent:SequentInPt) : Unit = {
		val b1 = boundsOfNode(comp)
		val yy = (b1.getMinY()).toInt-3
		var xmin = (b1.getMinX()).toInt
		var xmax = (b1.getMaxX()).toInt //+15


		for (child <- children(comp)) { 
			val b2 = boundsOfNode(child)
			if( (b2.getMinX()).toInt < xmin) xmin = (b2.getMinX()).toInt
			if( (b2.getMaxX()).toInt > xmax) xmax = (b2.getMaxX()).toInt
		}

		//g.drawLine( xmin, y, xmax+15, y )
		//g.drawLine( xmin+OFFSET_X, y+OFFSET_Y, xmax+OFFSET_X, y+OFFSET_Y )
		comp.ruleButton.peer.setLocation(xmax+5+OFFSET_X, yy-(comp.ruleIcon.getIconHeight/2)+OFFSET_Y)
		listenTo(comp.seqButton)
		listenTo(comp.ruleButton)

	}

	protected def add(comp: Component, x: Int, y: Int): Unit = {
		val p = comp.peer
		p.setLocation(x+OFFSET_X, y+OFFSET_Y)
		//comp.ruleButton.peer.setLocation(x+p.getPreferredSize.width+OFFSET_X, y+OFFSET_Y-p.getPreferredSize.height/2)
		//comp.ruleButton.peer.setSize(comp.ruleButton.peer.getPreferredSize)
		p.setSize(p.getPreferredSize)
		peer.add(p)
		listenTo(comp)

	}

	listenTo(mouse.clicks)
	reactions += {
		case ButtonClicked(b) =>
			b.text match {
				case "rule" =>
					val pressed = b.asInstanceOf[RuleInPtButton]
					if(pressed.parent.seqButton.visible){
						println("old bounds: " + boundsOfNode(pressed.parent))
						println("old height: " + pressed.parent.height)

						pressed.parent.contents -= pressed.parent.seqButton
						pressed.parent.preferredSize = pressed.parent.macroPtPanel.get.preferredSize
						pressed.parent.contents += pressed.parent.macroPtPanel.get
						println("new bounds: " + boundsOfNode(pressed.parent))
						println("new height: " + pressed.parent.height)

					} else {
						println("old bounds: " + boundsOfNode(pressed.parent))
						println("old height: " + pressed.parent.height)

						pressed.parent.contents -= pressed.parent.macroPtPanel.get
						pressed.parent.preferredSize = pressed.parent.seqButton.preferredSize
						pressed.parent.contents += pressed.parent.seqButton
						println("new bounds: " + boundsOfNode(pressed.parent))
						println("new height: " + pressed.parent.height)

					}
					pressed.parent.seqButton.visible = !pressed.parent.seqButton.visible

					repaint()
					//update()


				case "sequent" if editable =>
					unselect()
					val pressed = b.asInstanceOf[SequentInPtButton]
					/*println(b.text)
					println("Children:")
					for (child <- children(pressed)) { 
						println(child.text)
					}*/

					selectedSequentInPt = Some(pressed.parent)

					seqTreeViewDialog match {
						case Some(dialog) => 
							dialog.seqPanel.currentSequent = pressed.parent.seq
							dialog.seqPanel.rebuild()
						case None => 
					}

					pressed.border = Swing.LineBorder(Color.black)
					pressed.parent.sel = true
					//val b1 = boundsOfNode(pressed)
					popup.peer.show(b.peer, OFFSET_X, OFFSET_Y)
				case _ =>
					unselect()

			}
		case m : MouseClicked => 
			selectedSequentInPt = None
			println("unselect")
			unselect()

	}

	

	val popup = new PopupMenu

	val copy = new MenuItem(Action("Copy") {
		selectedSequentInPt match {
			case Some(seqIPT) => 
				// adapted from http://www.avajava.com/tutorials/lessons/how-do-i-copy-a-string-to-the-clipboard.html
				val str = sequentToString(seqIPT.seq, PrintCalc.ASCII)
				val toolkit = Toolkit.getDefaultToolkit()
				val clipboard = toolkit.getSystemClipboard()
				val strSel = new StringSelection(str)
				clipboard.setContents(strSel, null)
		}
		
	})
	popup.add(copy);

	
	val addAssm = new MenuItem(Action("Add as assm") {
		selectedSequentInPt match {
			case Some(seqIPT) => session.addAssm(seqIPT.seq)
		}
		
	})
	popup.add(addAssm);

	val merge = new MenuItem(Action("Merge above") {
		selectedSequentInPt match {
			case Some(selSeq) =>
				session.findMatches(selSeq.seq) match {
					case List() => 
						Dialog.showMessage(null, "No matching pt found!", "Error")
					case (x::xs) => 
						session.currentPT = session.mergePTs(x, selSeq, tree.getRoot(), children)
						session.savePT()

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
            				new PSDialog(depth=session.proofDepth, locale=session.currentLocale, seq=selSeq.seq).pt match {
	              				case Some(r) => 
	              					session.currentPT = session.mergePTs(r, selSeq, tree.getRoot(), children)
	              					session.savePT()

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
					val list = derAll(session.currentLocale, selSeq.seq, Nil, session.currentRuleList).filter{case (r, l) => r != RuleZera(Prem())} ++ derAllM(session.currentLocale, selSeq.seq, session.macroBuffer.toList)
					new SequentListDialog(list=list, session=session).pair match {
					/*new SequentInputDialog().sequent match {
						case Some(s) =>
							//println(selSeq.seq)
							//println(derAll(selSeq.seq).filter{ case (r,l) => l.exists(_ == s)})
							val pair = derAll(session.currentLocale, selSeq.seq).filter{ case (r,l) => l.exists(_ == s)} match {
								case List() => None
								case List((rule, derList)) => Some(rule, derList)
								case list => new RuleSelectDialog(list=list).pair 
							}

							pair match {*/
								case None => ;
								case Some((rule, derList)) =>
									val m = derList.map(x => Prooftreea(x, RuleZera(Prem()), List()) )
									val pt = rule match {
										case RuleZera(r) => m(0)
										case Fail() => m(0)
										case ru => Prooftreea( selSeq.seq, ru, m )
									}
									session.currentPT = session.mergePTs(pt, selSeq, tree.getRoot(), children)
									session.savePT()
									update()
						//	}
						//case None => Dialog.showMessage(null, "Invalid sequent entered", "Error")
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
							val pair = derAll(session.currentLocale, s).filter{ case (r,l) => l.exists(_ == selSeq.seq)} match {
								case List() => None
								case List((rule, derList)) => Some(rule, derList)
								case list => new RuleSelectDialog(list=list).pair 
							}

							pair match {
								case None => Dialog.showMessage(null, "No rule found for the given sequent", "Error")
								case Some((rule, derList)) =>
									val rest = session.rebuildFromPoint(selSeq, children)

									val intersection = derList.map(x => {if(x != concl(rest)) Prooftreea(x, RuleZera(Prem()), List()) else rest})
									session.currentPT = rule match {
										case RuleZera(r) => Prooftreea(s, RuleZera(r), List())
										case Fail() => Prooftreea(s, RuleZera(Prem()), List())
										case r => Prooftreea(s, r, intersection)
									}
									session.savePT()
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
	            	session.savePT()
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
	            	session.savePT()
	            	//update()
					
			}
		}
	})
	popup.add(delete2);


	def cut() = {
		selectedSequentInPt match {
			case Some(selSeq) =>
				if(tree.isLeaf(selSeq)) {
					new FormulaInputDialog().formula match {
			      		case Some(f) =>
							val lSeq = Sequenta(ant(selSeq.seq), Structure_Formula(f))
							val rSeq = Sequenta(Structure_Formula(f), consq(selSeq.seq))
							new PSDialog(depth=session.proofDepth, locale=session.currentLocale, seq=lSeq).pt match {
								case Some(resL) =>
									new PSDialog(depth=session.proofDepth, locale=session.currentLocale, seq=rSeq).pt match {
									  case Some(resR) =>
									  	val mPT = Prooftreea(selSeq.seq, RuleCuta(SingleCut()), List(resL, resR))
									    session.currentPT = session.mergePTs(mPT, selSeq, tree.getRoot(), children)
									    //session.currentPT = Prooftreea(selSeq.seq, RuleCuta(SingleCut()), List(resL, resR))
									    session.savePT()
										update()
									  case None => 
									    val res = Dialog.showConfirmation(null, 
									      "Right Tree not found. Should I add an assumption?", 
									      optionType=Dialog.Options.YesNo, title="Right tree not found")
									    if (res == Dialog.Result.Ok) {
									      session.addAssm(rSeq)
									      val resR = Prooftreea( rSeq, RuleZera(Prem()), List() )
									      val mPT = Prooftreea(selSeq.seq, RuleCuta(SingleCut()), List(resL, resR))
									      session.currentPT = session.mergePTs(mPT, selSeq, tree.getRoot(), children)
									      session.savePT()
										  update()
									    }
									}
								case None =>
									val res = Dialog.showConfirmation(null, 
									  "Left Tree not found. Should I add an assumption?", 
									  optionType=Dialog.Options.YesNo, title="Left tree not found")
									if (res == Dialog.Result.Ok) {
									  session.addAssm(lSeq)
									  val resL = Prooftreea( lSeq, RuleZera(Prem()), List() )
									  new PSDialog(depth=session.proofDepth, locale=session.currentLocale, seq=rSeq).pt match {
									    case Some(resR) =>
									      val mPT = Prooftreea(selSeq.seq, RuleCuta(SingleCut()), List(resL, resR))
									      session.currentPT = session.mergePTs(mPT, selSeq, tree.getRoot(), children)
									      //session.currentPT = Prooftreea(selSeq.seq, RuleCuta(SingleCut()), List(resL, resR))
									      session.savePT()
										  update()
									    case None => 
									      val res = Dialog.showConfirmation(null, 
									        "Right Tree not found. Should I add an assumption?", 
									        optionType=Dialog.Options.YesNo, title="Right tree not found")
									      if (res == Dialog.Result.Ok) {
									        session.addAssm(rSeq)
									        val resR = Prooftreea( rSeq, RuleZera(Prem()), List() )
									        val mPT = Prooftreea(selSeq.seq, RuleCuta(SingleCut()), List(resL, resR))
									      	session.currentPT = session.mergePTs(mPT, selSeq, tree.getRoot(), children)
									        //session.currentPT = Prooftreea(selSeq.seq, RuleCuta(SingleCut()), List(resL, resR))
									        session.savePT()
											update()
									      }
									  }
									}
							}
				    	case None => Dialog.showMessage(null, "Invalid formula!", "Formula Parse Error", Dialog.Message.Error)
				    }
				}
				else Dialog.showMessage(null, "The sequent is not a leaf please delete pt above to proceed", "Error")
		}
	}

	val cutt = new MenuItem(new Action("Apply Cut") {
		accelerator = Some(getKeyStroke('c'))
      	def apply = cut()
	})
	popup.add(cutt);

	val displaySeqTree = new MenuItem(new Action("Display Sequent tree") {
		accelerator = Some(getKeyStroke('t'))
      	def apply = {
      		seqTreeViewDialog match {
      			case None => 
      				val dialog = new SequentTreeViewDialog(null, selectedSequentInPt.get.seq)
      				seqTreeViewDialog = Some(dialog)
      			case Some(dialog) => 
      				dialog.seqPanel.currentSequent = selectedSequentInPt.get.seq
					dialog.seqPanel.rebuild()
					dialog.open()
      		}
      	}
	})
	popup.add(displaySeqTree);

	/*val replaceIntPT = new MenuItem(new Action("Replace into PT") {
      	def apply = {
      		selectedSequentInPt match {
			case Some(selSeq) =>
				session.findMatchesMacro(selSeq.seq) match {
					case List() => 
						Dialog.showMessage(null, "No matching pt found!", "Error")
					case (x::xs) =>
						session.currentPT = replaceIntoPT(selSeq.seq, x)
						session.addPT()

            			update()
            			//session.addPT()
				}
				
			}
		}
	})
	popup.add(replaceIntPT);*/


	def unselect(root:SequentInPt = tree.getRoot) : Unit = {
		root.seqButton.border = Swing.EmptyBorder(0,0,0,0)
		root.sel = false

		for (child <- children(root)) {
			//child.border = Swing.EmptyBorder(0,0,0,0)
			//child.sel = false
			unselect(child)
		}

	}

	def update() = {
		peer.removeAll()
		treeLayout = new TreeLayout[SequentInPt](createPTree(session.currentPT), nodeExtentProvider, configuration)
		build()
		peer.revalidate()
		peer.repaint()
		val s = treeLayout.getBounds().getBounds().getSize()
		preferredSize = new java.awt.Dimension(s.width + OFFSET_X*8, s.height + OFFSET_Y*2)
	}

	override def repaint() = {
		peer.removeAll()
		val old = treeLayout.getTree()
		treeLayout = new TreeLayout[SequentInPt](old, nodeExtentProvider, configuration)
		build()
		peer.revalidate()
		peer.repaint()
		val s = treeLayout.getBounds().getBounds().getSize()
		preferredSize = new java.awt.Dimension(s.width + OFFSET_X*8, s.height + OFFSET_Y*2)
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
		//parent.ruleIcon.paintIcon(null, g, xmax+5+OFFSET_X, y-(parent.ruleIcon.getIconHeight/2)+OFFSET_Y)
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
