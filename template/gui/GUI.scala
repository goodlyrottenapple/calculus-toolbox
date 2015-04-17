/*
TODO:

-- reimplement printCalcDef
-- reenable Cut

*/

import swing.{FileChooser, Orientation, Publisher, BoxPanel, FlowPanel, 
  Button, Dialog, Component, Swing, SimpleSwingApplication, TextField, Label, MenuBar, MenuItem, 
  Menu, BorderPanel, MainFrame, ScrollPane, Separator, Dimension, CheckMenuItem}
import swing.event.{ButtonClicked, MouseClicked, KeyReleased, Key}

import swing.BorderPanel.Position._

import scala.collection.JavaConversions._
import scala.collection.mutable.ListBuffer
import scala.util.parsing.json.{JSON, JSONObject, JSONArray}

import java.awt.FileDialog
import java.awt.event.MouseEvent
import javax.swing.{Icon, SpinnerNumberModel, JSpinner}
import javax.swing.filechooser.FileNameExtensionFilter
import javax.swing.event.{ChangeListener, ChangeEvent}

import java.io.PrintWriter

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants, TeXIcon}

/*calc_import*/
import Parser.{parseSequent, parseFormula, parseProoftree}
import PrintCalc._
import Proofsearch.derTree

object GUI extends SimpleSwingApplication {

  val AUTO_ADD_PT = "AUTO_ADD_PT"
  val AUTO_ADD_ASSM = "AUTO_ADD_ASSM"
  var globalPrefs = scala.collection.mutable.Map[String, Boolean]()

  var saveFile:Option[java.io.File] = None

  val session = CalcSession()
  //UI elements
  val inStr = new TextField { 
    text = "a |- a"
    columns = 25
  }
  
  val parsedStr = new Label { 
    val formula = new TeXFormula("a \\vdash a")
    icon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)    
  }

  //val log = new Label()
  val validPT = new Label("Valid Prooftree: ")
  val validPTval = new Label("true"){
    foreground = new java.awt.Color(101,163,44)
  }

  val addAssmButton = new Button {
    text = "Add assm"
  }

  val addPtButton = new Button {
    text = "Add PT"
    visible = false
  }

  /*val session.removeAssmButton = new Button {
    text = "Remove assm"
    enabled = false
  }

  val session.session.loadPTButton = new Button {
    text = "Load PT"
    enabled = false
  }

  val session.session.removePTsButton = new Button {
    text = "Remove PTs"
    enabled = false
  }
*/
  val reloadrelAKAButton = new Button {
    text = "Reload relAKA"
  }

  val loadLocButton = new Button {
    text = "Load Locale"
  }


  val numberModel = new SpinnerNumberModel(5, //initial value
    0, //min
    15, //max
    1) // who knows...
  val ptSearchHeightSpinner = new JSpinner(numberModel)

  ptSearchHeightSpinner.addChangeListener(new ChangeListener() {
    def stateChanged(e:ChangeEvent) {
      session.proofDepth = (ptSearchHeightSpinner.getValue()).asInstanceOf[Int]
    }
  })

  //define list of assms
  /*val session.listView = new ListView[(Icon, Sequent)]() {   
    listData = session.assmsBuffer
    renderer = ListView.Renderer(_._1)
  }

  //define list of found prooftrees
  val session.ptListView = new ListView[(Icon, Prooftree)]() {   
    listData = session.ptBuffer
    renderer = ListView.Renderer(_._1)
*/
  session.ptListView.listenTo(session.ptListView.mouse.clicks)
  session.ptListView.reactions += {
    case m : MouseClicked if !session.ptListView.selection.items.isEmpty && m.clicks == 2 => 
      session.loadPT
      ptPanel.update
    case m : MouseClicked if m.peer.getButton == MouseEvent.BUTTON3 => 
      val row = session.ptListView.peer.locationToIndex(m.peer.getPoint)
      if(row != -1) session.ptListView.peer.setSelectedIndex(row)
      if(!session.ptListView.selection.items.isEmpty) popup.peer.show(m.peer.getComponent, m.peer.getX, m.peer.getY)
  }
//  }


  val popup = new PopupMenu
  val menuItem = new MenuItem(swing.Action("Add as assm") {
    session.addAssmFromSelPT()
  })
  popup.add(menuItem);
  val menuItem2 = new MenuItem(swing.Action("Delete") {
    session.removePTs()
    session.ptListView.revalidate()
    session.ptListView.repaint()
  })
  popup.add(menuItem2);

  val menuItem3 = new MenuItem(swing.Action("Export to LaTeX") {
    session.exportLatexFromSelPT()

  })
  popup.add(menuItem3);

  val menuItem4 = new MenuItem(swing.Action("Create Rule Macro") {
    session.rulifyPT()
  })
  popup.add(menuItem4);



  session.macroListView.listenTo(session.macroListView.mouse.clicks)
  session.macroListView.reactions += {
    case m : MouseClicked if !session.macroListView.selection.items.isEmpty && m.clicks == 2 => 
      val sel = session.macroListView.selection.items.head
      new MacroAddDialog(macroName = sel._1, pt=sel._2, adding=false)
    case m : MouseClicked if m.peer.getButton == MouseEvent.BUTTON3 => 
      val row = session.macroListView.peer.locationToIndex(m.peer.getPoint)
      if(row != -1) session.macroListView.peer.setSelectedIndex(row)
      if(!session.macroListView.selection.items.isEmpty) popupMacro.peer.show(m.peer.getComponent, m.peer.getX, m.peer.getY)
  }
//  }


  val popupMacro = new PopupMenu
  val macroItem = new MenuItem(swing.Action("Save Macros") {
    val fd = new FileDialog(null: java.awt.Dialog, "Save a macro file", FileDialog.SAVE)
    fd.setDirectory(".")
    fd.setFilenameFilter(new CSFilter())
    fd.setVisible(true)
    val filename = fd.getFile()
    if (filename != null){
      val file = if (!filename.endsWith(".cs")) new java.io.File(fd.getDirectory() + filename + ".cs") else new java.io.File(fd.getDirectory() + filename)
      saveFile = Some(file)
      saveLocaleFile(saveFile.get)
    }
    else
      println("Cancelled")
  })
  popupMacro.add(macroItem)
  

  // ptPanel stuff here
  val ptPanel = new ProofTreePanel(session)
  ptPanel.build()

  //add components to listener here

  listenTo(loadLocButton, session, session.listView.keys, session.ptListView.keys, inStr.keys, addAssmButton, addPtButton, reloadrelAKAButton) //session.addAssmButton, session.removeAssmButton, session.removePTsButton, session.loadPTButton, session.addPtButton, 
  reactions += {
    //case c : MacroAdded => println("added macro")
    case c : PTChanged => 
      validPTval.text = c.valid.toString
      if (c.valid) validPTval.foreground = new java.awt.Color(101,163,44)
      else validPTval.foreground = new java.awt.Color(211,51,63)

    case KeyReleased(session.listView, Key.BackSpace, _, _) => session.removeAssms
    case KeyReleased(session.listView, Key.Delete, _, _) => session.removeAssms
    case KeyReleased(session.ptListView, Key.BackSpace, _, _) => session.removePTs
    case KeyReleased(session.ptListView, Key.Delete, _, _) => session.removePTs
    case KeyReleased(session.ptListView, Key.Enter, _, _) => 
      session.loadPT
      ptPanel.update

    case KeyReleased(`inStr`, k, _, _) =>
      parseSequent(inStr.text) match {
        case Some(r) => {
          session.currentSequent = r
          val latex = sequentToString(r)
          val formula = new TeXFormula(latex)
          parsedStr.icon = formula.createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)

          if(k == Key.Enter){
            println("ASCII: " + sequentToString(session.currentSequent, PrintCalc.ASCII))
            println("LATEX: " + sequentToString(session.currentSequent, PrintCalc.LATEX))
            println("ISABELLE: " + sequentToString(session.currentSequent, PrintCalc.ISABELLE))
            println("RULE: " + sequentToString(rulifySequent(session.currentSequent), PrintCalc.ASCII))
            //val currentValue:Int = (ptSearchHeightSpinner.getValue).asInstanceOf[Int] //nasty hack!!
            //val currentAssm = session.assmsBuffer.toList.map({case (i,s) => Premise(s)})
            //derTree(currentValue, session.currentLocale++currentAssm, session.currentSequent) match {
            new PSDialog(depth=session.proofDepth, locale=session.currentLocale, seq=session.currentSequent).pt match {
              case Some(r) =>
                session.currentPT = r
                //display prooftree r in the PTPanel
                ptPanel.update()
                //log.text = "PT found!"
                //validPT.text = "Valid PTwCut: " + isProofTree(session.currentLocale, session.currentPT)
                //add pt to the list of found proofs
                if(globalPrefs(AUTO_ADD_PT) == true){
                  session.addPT()
                  if(globalPrefs(AUTO_ADD_ASSM) == true) session.addAssm()
                } //else session.currentPTsel = None
                case None => Dialog.showMessage(null, "No Prooftree could be found...", "Error")
            }
          }
        }
          
        case None => ;
      }
    
    case ButtonClicked(`addPtButton`) => session.addPT()
    case ButtonClicked(`addAssmButton`) => session.addAssm()


    case ButtonClicked(`loadLocButton`) =>
      val fd = new FileDialog(null: java.awt.Dialog, "Open a macro file", FileDialog.LOAD)
      fd.setDirectory(".")
      fd.setFilenameFilter(new CSFilter())
      fd.setVisible(true)
      val filename = fd.getFile()
      if (filename != null) {
        val file = new java.io.File(fd.getDirectory() + filename)
        openLocaleFile(file)
      }

    case ButtonClicked(`reloadrelAKAButton`) =>
      val buff = scala.collection.mutable.Map[Tuple2[Action, Agent], List[Action]]()
      for (l <- scala.io.Source.fromFile("relAKA.txt").getLines){
        val arr = l.split(",")
        if (arr.length == 3) {
          val alpha = Actiona(arr(0).trim.toList)
          val a = Agenta(arr(1).trim.toList)
          val beta = Actiona(arr(2).trim.toList)

          buff.get((alpha, a)) match {
            case Some(list) => buff += ((alpha, a) -> (list ++ List(beta)))
            case None => buff += ((alpha, a) -> List(beta))
          }
          session.currentPT = session.currentPT

        }
      }
      session.relAKAMap = buff.toMap
      for (l <- scala.io.Source.fromFile("relAKA.txt").getLines){
        val arr = l.split(",")
        if (arr.length == 3) {
          val alpha = Actiona(arr(0).trim.toList)
          val a = Agenta(arr(1).trim.toList)
          val beta = Actiona(arr(2).trim.toList)

          println(session.relAKA(alpha)(a))

        }
      }
  }

  //UI element spositioning in the main window 
  lazy val topPanel = new BorderPanel{
    layout (inStr) = Center
    layout (parsedStr) = East

    border = Swing.EmptyBorder(10, 10, 10, 10)
  }

  lazy val assmsPanel = new BoxPanel(Orientation.Vertical){
    preferredSize = new java.awt.Dimension(250, 600)
    contents += new Label("Assms:")
    contents += new ScrollPane(session.listView) //{horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always}
    contents += addAssmButton//new FlowPanel(session.addAssm)//,removeAssm)
    contents += new Label("PTs:")
    contents += new ScrollPane(session.ptListView) //{horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always}
    contents += addPtButton//new FlowPanel(addPt,session.loadPT,session.removePTs)

    contents += new Label("Macros:")
    contents += new ScrollPane(session.macroListView) //{horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always}

    border = Swing.EmptyBorder(0, 0, 0, 10)
  }

  lazy val bottomPanel = new FlowPanel {
    contents += loadLocButton
    contents += reloadrelAKAButton
    contents += new Label("PT search depth:")
    contents += Component.wrap(ptSearchHeightSpinner)
    //contents += log
    contents += validPT
    contents += validPTval
    border = Swing.EmptyBorder(0,0,0,0)
  }


  lazy val ui = new BorderPanel{
    layout (topPanel) = North
    layout (new ScrollPane(ptPanel){border = Swing.EmptyBorder(0, 0, 0, 0)}) = Center
    layout (bottomPanel) = South
    layout (assmsPanel) = East

    border = Swing.EmptyBorder(0, 0, 0, 0)
  }

  def openCSFile(file:java.io.File) = {
    val jsonStr = scala.io.Source.fromFile(file).getLines.mkString
    Some(JSON.parseFull(jsonStr)) match {
      case Some(M(map))  =>
        map.get("assms") match {
          case L(assms) =>
            val ass = assms.map(parseSequent(_))
            session.clearAssms
            for (Some(a) <- ass){
              session.addAssm(a)
            }
          case _ => ;
        }
        map.get("pts") match {
          case L(pts) =>
            val ptss = pts.map(parseProoftree(_))
            session.clearPT
            for (Some(pt) <- ptss){
              session.addPT(pt)
            }
          case _ => ;
        }
      case _ => ;
    }
  }

  def openLocaleFile(file:java.io.File) = {
    val jsonStr = scala.io.Source.fromFile(file).getLines.mkString
    Some(JSON.parseFull(jsonStr)) match {
      case Some(M(map))  =>
        map.get("macros") match {
          case MM(macros) =>
            val mac = macros.map{case (k, v) => (k, parseProoftree(v))}
            //session.clearAssms
            for ((k, Some(m)) <- mac){
              //println(m)
              session.macroBuffer += Tuple2(k, m)
            }
            session.macroListView.listData = session.macroBuffer
          case _ => ;
        }
      case _ => ;
    }
  }

  def saveCSFile(file:java.io.File) = {  
    Some(new PrintWriter(file)).foreach{p =>
      p.write(
        JSONObject( 
          Map( 
            "assms" -> JSONArray( session.assmsBuffer.toList.map{case (i,s) => sequentToString(s, PrintCalc.ASCII)} ),
            "pts"   -> JSONArray( session.ptBuffer.toList.map{case (i,s) => prooftreeToString(s, PrintCalc.ASCII)} )   ) )
          .toString())
      p.close
    }
  }

  def saveLocaleFile(file:java.io.File) = {  
    Some(new PrintWriter(file)).foreach{p =>
      p.write(
        JSONObject( 
          Map( 
            "macros" -> JSONObject(session.macroBuffer.map{case (n, pt) => (n, prooftreeToString(pt, PrintCalc.ASCII))}.toMap)
            //"pts"   -> JSONArray( session.ptBuffer.toList.map{case (i,s) => prooftreeToString(s, PrintCalc.ASCII)} )   
          ) ).toString())
      p.close
    }
  }

  def top = new MainFrame {
    title = "Calculus Toolbox"
    contents = ui
    minimumSize = new Dimension(600,400)

    System.setProperty("apple.laf.useScreenMenuBar", "true")

    menuBar = new MenuBar {
      contents += new Menu("File") {
        contents += new MenuItem(swing.Action("Open..."){
          /*val chooser = new FileChooser(new java.io.File(".")) {
            title = "Open Calc Session File"
            fileFilter = new FileNameExtensionFilter("Calculus session", "cs")
          }
          val result = chooser.showOpenDialog(null)
          if (result == FileChooser.Result.Approve) openCSFile(chooser.selectedFile)
          //println(res)*/
          val fd = new FileDialog(null: java.awt.Dialog, "Open a session file", FileDialog.LOAD)
          fd.setDirectory(".")
          fd.setFilenameFilter(new CSFilter())
          fd.setVisible(true)
          val filename = fd.getFile()
          if (filename != null) {
            val file = new java.io.File(fd.getDirectory() + filename)
            openCSFile(file)
            saveFile = Some(file)
          }
          else
            println("Cancelled");
        })
        contents += new MenuItem(swing.Action("Save") {
          println("Action '"+ title +"' invoked")
          if(saveFile == None){
            /*val chooser = new FileChooser(new java.io.File(".")) {
              title = "Save Calc Session File"
              fileFilter = new FileNameExtensionFilter("Calculus session", "cs")
            }
            val result = chooser.showSaveDialog(null)*/
            val fd = new FileDialog(null: java.awt.Dialog, "Save a session file", FileDialog.SAVE)
            fd.setDirectory(".")
            fd.setFilenameFilter(new CSFilter())
            fd.setVisible(true)
            val filename = fd.getFile()
            if (filename != null){
              val file = if (!filename.endsWith(".cs")) new java.io.File(fd.getDirectory() + filename + ".cs") else new java.io.File(fd.getDirectory() + filename)
              saveFile = Some(file)
              saveCSFile(saveFile.get)
            }
            else
              println("Cancelled")
          } else saveCSFile(saveFile.get)
          
        })


        contents += new MenuItem(swing.Action("Save As...") {
          println("Action '"+ title +"' invoked")
          
          /*val chooser = new FileChooser(new java.io.File(".")) {
            title = "Save Calc Session File"
            fileFilter = new FileNameExtensionFilter("Calculus session", "cs")
          }
          val result = chooser.showSaveDialog(null)
          if (result == FileChooser.Result.Approve) {
              val file = if (!chooser.selectedFile.toString.endsWith(".cs")) new java.io.File(chooser.selectedFile.toString+".cs") else chooser.selectedFile
              saveFile = Some(file)
              saveCSFile(file)
          }*/
          val fd = new FileDialog(null: java.awt.Dialog, "Save a session file", FileDialog.SAVE)
          fd.setDirectory(".")
          fd.setFilenameFilter(new CSFilter())
          fd.setVisible(true)
          val filename = fd.getFile()
          if (filename != null){
            val file = if (!filename.endsWith(".cs")) new java.io.File(fd.getDirectory() + filename + ".cs") else new java.io.File(fd.getDirectory() + filename)
            saveFile = Some(file)
            saveCSFile(saveFile.get)
          }
          else
            println("Cancelled");
        })
        contents += new Separator
        contents += new MenuItem(swing.Action("Quit") {
          System.exit(1)
          //accelerator = Some(KeyStroke.getKeyStroke("ctrl S"))
        })
      }
      contents += new Menu("Options") {
        val aaPT = new CheckMenuItem("Auto-add PT's") {
          //this.tooltip = tooltip; 
          selected = !addPtButton.visible
          globalPrefs += (AUTO_ADD_PT -> selected)
        }
        contents += aaPT
        val aaAssm = new CheckMenuItem("Auto-add Assms") {
          //this.tooltip = tooltip; 
          selected = false
          globalPrefs += (AUTO_ADD_ASSM -> selected)
        }
        contents += aaAssm
        listenTo(aaPT, aaAssm)
        reactions += {
          case ButtonClicked(`aaPT`) => 
            globalPrefs += (AUTO_ADD_PT -> aaPT.selected)
            addPtButton.visible = !aaPT.selected
            revalidate()
            repaint()
          case ButtonClicked(`aaAssm`) => 
            globalPrefs += (AUTO_ADD_ASSM -> aaAssm.selected)
        }

        /*contents += new Separator
        contents += new MenuItem(swing.Action("Generate LaTeX calc decription file") {
          Some(new PrintWriter("calc_description.tex")).foreach{p =>
            val c_def = ""//printCalcDef()
            p.write( s"\\documentclass[12pt]{article}\n\\usepackage{bussproofs}\n\n\\begin{document}\n\n$c_def\n\n\\end{document}" )
            p.close
          }
          //accelerator = Some(KeyStroke.getKeyStroke("ctrl S"))
        })*/
      }
      
    }
  }
}

class CSFilter extends java.io.FilenameFilter {
  def accept(directory: java.io.File, filename : String): Boolean = {
    if (filename.endsWith(".cs")) return true
    return false
  }
}

object M extends CC[Map[String, Any]]
object MM extends CC[Map[String, String]]