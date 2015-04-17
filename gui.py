#!/usr/bin/env python
import npyscreen, curses, os
from tools import utils


class MyTestApp(npyscreen.NPSAppManaged):

    def onStart(self):
        # When Application starts, set up the Forms that will be used.
        # These two forms are persistent between each edit.
        self.addForm("MAIN",       MainForm, name="Calculus Toolbox v0.2", color="IMPORTANT",)
        self.addForm("Build Calculus",     BuildForm, name="Build Calculus", color="IMPORTANT",  )
        self.addForm("Debug Tools",     DebugForm, name="Debug Tools", color="WARNING",  )
        # This one will be re-created each time it is edited.
        #self.addFormClass("THIRD", MainForm, name="Screen 3", color="CRITICAL",)
        

    def change_form(self, name):
        # Switch forms.  NB. Do *not* call the .edit() method directly (which 
        # would lead to a memory leak and ultimately a recursion error).
        # Instead, use the method .switchForm to change forms.
        self.switchForm(name)
        
        # By default the application keeps track of every form visited.
        # There's no harm in this, but we don't need it so:        
        self.resetHistory()
    
class MainForm(npyscreen.ActionFormMinimal):
    def create(self):
        self.add(npyscreen.FixedText, value = "Select operation:")
        # self.add(MyButton, name = 'Build Calculus', relx = 2,rely= 5)
        self.add(MyButton, name = 'Debug Tools', relx = 2,rely= 5)

    def on_ok(self):
        # Exit the application if the OK button is pressed.
        self.parentApp.switchForm(None)

class MyButton(npyscreen.MiniButtonPress):
    def whenPressed(self):
        self.parent.parentApp.switchForm(self.name)



class BuildForm(npyscreen.ActionFormMinimal):
    def create(self):
        self.fn = self.add(npyscreen.TitleFilenameCombo, name = "Calculus file:",)
        self.fn.value = os.getcwd() + "/default.json"
        self.out = self.add(npyscreen.TitleFilenameCombo, name = "Output folder:",  select_dir=True,)

        

    def on_ok(self):
        # Exit the application if the OK button is pressed.
        self.parentApp.switchForm("MAIN")

    def change_forms(self, *args, **keywords):
        self.text.value = args



class DebugForm(npyscreen.ActionFormMinimal):
    def create(self):
        self.add(npyscreen.FixedText, value = "Test build on single file...")

        self.fn = self.add(npyscreen.TitleFilenameCombo, name = "Calc file:", rely=4)
        self.fn.value = os.getcwd() + "/default.json"
        self.out = self.add(npyscreen.TitleFilenameCombo, name = "Out folder:",  select_dir=True,)
        self.out.value = os.getcwd() + "/export/"
        self.input = self.add(npyscreen.TitleFilenameCombo, name = "Input file:",  )
        self.input.value = os.getcwd() + "/template/"

        self.build = self.add(npyscreen.ButtonPress, name = 'Build' ,rely= 8)
        self.build.whenPressed = self.doBuild

        self.reload = self.add(npyscreen.ButtonPress, name = 'Reload Builder' , rely=8, relx= 10)
        self.reload.whenPressed = self.doReload

        self.add(npyscreen.FixedText, value = "Test unbuild on single file..." , rely=10)

        self.out2 = self.add(npyscreen.TitleFilenameCombo, name = "Out folder:",  select_dir=True , rely=12)
        self.out2.value = os.getcwd() + "/clean/"
        self.input2 = self.add(npyscreen.TitleFilenameCombo, name = "Input file:",  )
        self.input2.value = os.getcwd() + "/export/"

        self.unbuild = self.add(npyscreen.ButtonPress, name = 'Un-Build' , rely= 15)
        self.unbuild.whenPressed = self.doUnbuild

        
    def on_ok(self):
        # Exit the application if the OK button is pressed.
        self.parentApp.switchForm("MAIN")

    def doReload(self, *args):
        from tools import isabuilder, scalabuilder
        try:
            isabuilder = reload(isabuilder)
            scalabuilder = reload(scalabuilder)
        except Exception, e:
            npyscreen.notify_confirm(str(e))

    def doBuild(self, *args):
        try:
            if os.path.isfile(self.input.value):
                out_path = self.input.value.split("/")[-1]
                file_type = self.input.value.split(".")[-1]
                from tools import isabuilder, scalabuilder

                if file_type == "thy":
                    isaBuild = isabuilder.IsabelleBuilder(self.fn.value)
                    if "_" in out_path: out_path = isaBuild.get("calc_name") + "_" + out_path.split("_")[-1]
                    else: out_path = isaBuild.get("calc_name") + "." + file_type
                    utils.writeFile(self.out.value+"/"+out_path, utils.processFile(utils.readFile(self.input.value), isaBuild, "(*", "*)"))
                elif file_type == "scala":
                    scalaBuild = scalabuilder.ScalaBuilder(self.fn.value)
                    scalaBuild.add("core_compiled", "")
                    
                    utils.writeFile(self.out.value+"/"+out_path, utils.processFile(utils.readFile(self.input.value), scalaBuild, "/*", "*/"))
                else:
                    npyscreen.notify_confirm("Error input file not supported!")

            else:
                npyscreen.notify_confirm("Error no input file selected!")
        except Exception, e: # catch *all* exceptions
            npyscreen.notify_confirm(str(e))

    

    def doUnbuild(self, *args):
        if os.path.isfile(self.input2.value):
            out_path = self.input2.value.split("/")[-1]
            file_type = self.input2.value.split(".")[-1]
            if file_type == "thy":
                utils.writeFile( self.out2.value+"/"+out_path, utils.revert( utils.readFile(self.input2.value), "(*", "*)" ) )
            elif file_type == "scala":
                utils.writeFile( self.out2.value+"/"+out_path, utils.revert( utils.readFile(self.input2.value), "/*", "*/" ) )
            else:
                npyscreen.notify_confirm("Error input file not supported!")

        else:
            npyscreen.notify_confirm("Error no input file selected!")
    

def main():
    TA = MyTestApp()
    TA.run()


if __name__ == '__main__':
    main()
