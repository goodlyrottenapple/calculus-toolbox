import swing.{Button, Swing}

import java.awt.Dimension
import javax.swing.SwingConstants

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants}

/*calc_import*/
import PrintCalc.{sequentToString, formulaToString, ruleToString}
import Parser.parseSequent

class SequentInPt(val seq:Sequent, val rule:Rule, size:Int = 15, val cutFormula:Option[Formula] = None, 
  abbrevMap:Map[String, String] = Map()) extends Button {

	//val latXForm = new TeXFormula(sequentToString(seq))
    //icon = latXForm.createTeXIcon(TeXConstants.STYLE_DISPLAY, size)
    updateIcon(abbrevMap)
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

    def updateIcon(abbrevMap:Map[String, String] = Map()) = {
    	var text = sequentToString(seq, PrintCalc.ASCII).replaceAll(" ","")
    	println(text)
    	println(abbrevMap)

      //println(abbrevMap.keys.toList.sortBy(abbrevMap(_).length).reverse)
    	for(k <- abbrevMap.keys.toList.sortBy(abbrevMap(_).length))
        if(text contains abbrevMap(k).replaceAll(" ", "")) text = text.replaceAllLiterally(abbrevMap(k).replaceAll(" ", ""), k)

      text = parseSequent(text) match {
    		case Some(seq) => sequentToString(seq)
    		case None => "error"
    	}
    	val latXForm = new TeXFormula(text)
   		icon = latXForm.createTeXIcon(TeXConstants.STYLE_DISPLAY, size)
    }

}