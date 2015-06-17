import swing.{Button, Swing}

import java.awt.Dimension
import javax.swing.SwingConstants

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants}

/*calc_import*/
import PrintCalc.{sequentToString, formulaToString, ruleToString}
import Parser.parseSequent

class SequentInPt(val seq:Sequent, val rule:Rule, size:Int = 15, val cutFormula:Option[Formula] = None, 
  session:CalcSession = CalcSession()) extends Button {

	//val latXForm = new TeXFormula(sequentToString(seq))
    //icon = latXForm.createTeXIcon(TeXConstants.STYLE_DISPLAY, size)
  icon = session.sequentToIcon(seq)
	
  val width: Int = icon.getIconWidth//()//+5
	val height: Int = icon.getIconHeight//()
	val ruleIcon = cutFormula match {
		case None => 
			val ruleTex = new TeXFormula(ruleToString(rule))
			ruleTex.createTeXIcon(TeXConstants.STYLE_DISPLAY, .7f*size)
		case Some(form) =>
			val ruleTex = new TeXFormula(ruleToString(rule) + "(" + formulaToString(form) +")")
			ruleTex.createTeXIcon(TeXConstants.STYLE_DISPLAY, .7f*size)
	}

	var sel = false
	
	text = seq.toString
	border = Swing.EmptyBorder(0, 0, 0, 0)
	val s = new Dimension(width, height)
	//minimumSize = s
  //maximumSize = s
  preferredSize = s
  peer.setHorizontalAlignment(SwingConstants.LEFT)


}