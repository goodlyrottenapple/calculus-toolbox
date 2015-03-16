import swing._
import swing.event.{KeyReleased, Key, SelectionChanged}
import swing.BorderPanel.Position._
import swing.ListView.IntervalMode
import javax.swing.Icon

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants, TeXIcon}

/*calc_import*/
import Parser.{parseSequent, parseFormula}
import PrintCalc._

class FormulaInputDialog(owner: Window = null) extends Dialog(owner) {
  var formula:Option[Formula] = None
  modal = true

  val in = new TextField { 
    text = ""
    columns = 25
    //horizontalAlignment = Alignment.Right
  }
  
  val inL = new Label

  listenTo(in.keys)
  reactions += {
    case KeyReleased(`in`, k, _, _) =>
      parseFormula(in.text) match {
        case Some(r) =>
          formula = Some(r)
          val latex = formulaToString(r)
          inL.icon = new TeXFormula(latex).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
        case None => ;
      }
  }

  contents = new BorderPanel {
    layout(new BoxPanel(Orientation.Horizontal) {
      border = Swing.EmptyBorder(5,5,5,5)

      contents += in
      contents += inL
    }) = Center

    layout(new FlowPanel(FlowPanel.Alignment.Right)( Button("Use Formula") { close() } )) = South
  }

  centerOnScreen()
  open()
}

class SequentInputDialog(owner: Window = null) extends Dialog(owner) {
  var sequent:Option[Sequent] = None
  modal = true

  val in = new TextField { 
    text = ""
    columns = 25
    //horizontalAlignment = Alignment.Right
  }
  
  val inL = new Label

  listenTo(in.keys)
  reactions += {
    case KeyReleased(`in`, Key.Enter, _, _) =>
      close()
    case KeyReleased(`in`, k, m, _) =>
      parseSequent(in.text) match {
        case Some(r) =>
          sequent = Some(r)
          val latex = sequentToString(r)
          inL.icon = new TeXFormula(latex).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
        case None => ;
      }

  }

  contents = new BorderPanel {
    layout(new BoxPanel(Orientation.Horizontal) {
      border = Swing.EmptyBorder(5,5,5,5)

      contents += in
      contents += inL
    }) = Center

    layout(new FlowPanel(FlowPanel.Alignment.Right)( Button("Use Sequent") { close() } )) = South
  }

  centerOnScreen()
  open()
}

class RuleSelectDialog(owner: Window = null, list : List[(Rule, List[Sequent])] ) extends Dialog(owner) {
  var pair:Option[(Rule, List[Sequent])] = None
  modal = true

  val listView = new ListView[(Icon, Rule, List[Sequent])]() {   
    listData = for((r,l) <- list) yield (new TeXFormula(ruleToString(r)).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15), r, l)
    renderer = ListView.Renderer(_._1)
    selection.intervalMode = IntervalMode.Single
  }

  val b = new Button("Select Rule") { 
    enabled = false 
  } 

  listenTo(listView.selection)
  reactions += {
    case SelectionChanged(`listView`) =>
      val sel = listView.selection.items(0)
      pair = Some((sel._2, sel._3))
      if(!b.enabled){
        b.enabled = true
        b.action = Action("Select Rule"){close()}
      }
  }

  contents = new BorderPanel {
    layout(new Label("Select a rule to apply:")) = North

    layout(listView) = Center

    layout(new FlowPanel(FlowPanel.Alignment.Right)( b )) = South
  }

  centerOnScreen()
  open()
}