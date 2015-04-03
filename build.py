#!/usr/bin/env python
import os,sys,getopt,shlex,shutil
from subprocess import Popen, PIPE
from glob import glob
from tools import utils, isabuilder, scalabuilder

CALC_NAME = ""
CALC_TEMPLATE = "default.json"
OUTPUT_PATH = "gen_calc/"
TEMPLATE_FILES_PATH = "template/"
LIB_FILES_PATH ="libs/"

SCALA_SRC_PATH = "src/scala/"
ISABELLE_SRC_PATH = "src/isabelle/"

PARSER_TEMPLATE = "Parser"
#RULE_GEN_TEMPLATE = "Rule_Gen"
PRINT_TEMPLATE = "Print"
ISA_CORE_TEMPLATE = "Calc_Core"
ISA_RULES_TEMPLATE = "Calc_Rules"

#calculate relative path from path1 to path2 (assuming they are prefixed by the same path)
def nav_to_folder(path1, path2):
    out = ""
    split_path2 = path2.split("/")[:-1]
    matched = False
    for i in reversed(path1.split("/")[:-1]):
        if i in split_path2 and path2.startswith(path1.split(i)[0]):
            matched = True
            out += path2.split(i+"/")[1]
        else: out += "../"

    if not matched: out += path2
    return out

def cmd_output_throws_error(flags, response, err, error_msg):
    if "error" in response.lower() or "bad session" in response.lower() or "unfinished session" in response.lower():
        if "verbose" in flags: print response
        print "ERROR :", error_msg
        return True
    if err is not None and ("error" in err.lower() or "bad session" in err.lower()):
        if "verbose" in flags: print err
        print "ERROR :", error_msg
        return True
    if "verbose" in flags: print response
    return False

def usage():
    print "This is a Display Calculus project build script v0.2"
    usage = ["Usage:"]
    usage.append( "-c  --calc                                       Specify a calculus file. Defaults to '{0}'".format(CALC_TEMPLATE) )
    usage.append( "-p  --path                                       Specify an output path for the calculus. Defaults to '{0}'".format(OUTPUT_PATH) )
    usage.append( "-t  --template                                   Specify a templates folder to be used. Defaults to '{0}'".format(TEMPLATE_FILES_PATH) )
    usage.append( "-f  --force                                      Force recompile (use if isa files generation fails)" )
    usage.append( "-v  --verbose                                    Verbose mode" )
    usage.append( "-b  --build     {all, scala, isabelle}           Compile only selected files. Defaults to 'all' flag" )
    usage.append( "-s  --stage     {core_calc_gen, calc_compile,    Call a specific stage of the build\n                rule_calc_gen, add_gui}    " )

    print "\n".join(usage)


def doBuild(builder, in_path, out_path):
    try:
        file_type = in_path.split(".")[-1]

        if file_type == "thy":
            utils.writeFile(out_path, utils.processFile(utils.readFile(in_path), builder, "(*", "*)"))
            return True
        elif file_type == "scala":
            utils.writeFile(out_path, utils.processFile(utils.readFile(in_path), builder, "/*", "*/"))
            return True
        else:
            print "Error no input file selected!"
            return False
    except Exception, e: # catch *all* exceptions
        print str(e)
        return False

def core_calc_gen(flags):
    print "################# Generating core calculus files ##################"
    builder = scalabuilder.ScalaBuilder(CALC_TEMPLATE)
    CALC_NAME = builder.get("calc_name")

    if "all" in flags or "scala" in flags :
        #create scala src folder
        if not os.path.exists(OUTPUT_PATH + SCALA_SRC_PATH):
            os.makedirs(OUTPUT_PATH + SCALA_SRC_PATH)

        paths = glob(TEMPLATE_FILES_PATH + '*.scala')
        list = [p.split('/')[-1].split('.')[0] for p in paths]

        if PARSER_TEMPLATE in list:
            print "Generating parser from", paths[list.index(PARSER_TEMPLATE)], "..."
            if not doBuild(builder,paths[list.index(PARSER_TEMPLATE)], OUTPUT_PATH+SCALA_SRC_PATH+PARSER_TEMPLATE+".scala"): return False
            #args = [CALC_TEMPLATE, "parser", paths[list.index(PARSER_TEMPLATE)], OUTPUT_PATH+SCALA_SRC_PATH+PARSER_TEMPLATE+".scala"]
            #cmd = "scala -classpath bin:. CalcGenerator " + " ".join(args)
            #response,err = Popen(shlex.split(cmd), stdout=PIPE).communicate()
            #if cmd_output_throws_error(flags, response, err, "Generating parser class failed!"): return False

        if PRINT_TEMPLATE in list:
            print "Generating print class from", paths[list.index(PRINT_TEMPLATE)], "..."
            if not doBuild(builder,paths[list.index(PRINT_TEMPLATE)], OUTPUT_PATH+SCALA_SRC_PATH+PRINT_TEMPLATE+".scala"): return False

    if "all" in flags or "isabelle" in flags :
        #create isabelle src folder
        if not os.path.exists(OUTPUT_PATH + ISABELLE_SRC_PATH):
            os.makedirs(OUTPUT_PATH + ISABELLE_SRC_PATH)

        paths = glob(TEMPLATE_FILES_PATH + '*.thy')
        list = [p.split('/')[1].split('.')[0] for p in paths]
        builder = isabuilder.IsabelleBuilder(CALC_TEMPLATE)
        builder.add("export_path", nav_to_folder(ISABELLE_SRC_PATH, SCALA_SRC_PATH))

        if ISA_CORE_TEMPLATE in list:
            print "Generating core calculus from", paths[list.index(ISA_CORE_TEMPLATE)], "..."
            if not doBuild(builder, paths[list.index(ISA_CORE_TEMPLATE)], OUTPUT_PATH+ISABELLE_SRC_PATH+CALC_NAME+"_Core.thy"): return False
            utils.generateIsaROOT(CALC_NAME+"_Core", OUTPUT_PATH+ISABELLE_SRC_PATH)
            
            print "Compiling Isabelle source files in", OUTPUT_PATH + ISABELLE_SRC_PATH, "..."
            if "force" in flags:
              cmd = "isabelle build -D " + OUTPUT_PATH + ISABELLE_SRC_PATH + " -c"
            else:
              cmd = "isabelle build -D " + OUTPUT_PATH + ISABELLE_SRC_PATH
            #print cmd
            response,err = Popen(shlex.split(cmd), stdout=PIPE, stderr=PIPE).communicate()
            if cmd_output_throws_error(flags, response, err, "Generating calculus scala file failed!"): return False

    return True
    


def calc_compile(flags):
    builder = scalabuilder.ScalaBuilder(CALC_TEMPLATE)
    CALC_NAME = builder.get("calc_name")
    if "final" in flags: print "################ Recompiling core calculus files ##################"
    else: print "################# Compiling core calculus files ###################"

    paths = glob(OUTPUT_PATH + SCALA_SRC_PATH + '*.scala')
    list = [p.split('/')[-1].split('.')[0] for p in paths]

    if CALC_NAME not in list:
        print "ERROR : Missing the core calculus file! Try re-builidng with -f to rebuild the calculus"
        return False
    if "verbose" in flags: print "Compiling:", paths

    #create bin folder in OUTPUT_PATH
    if not os.path.exists(OUTPUT_PATH + "bin"):
        os.makedirs(OUTPUT_PATH + "bin")
    elif "force" in flags:
        shutil.rmtree(OUTPUT_PATH + "bin")
        os.makedirs(OUTPUT_PATH + "bin")

    cmd = "scalac -J-Xmx1024m -d " + OUTPUT_PATH + "bin -classpath . " + " ".join(paths)
    print cmd
    response,err = Popen(shlex.split(cmd), stdout=PIPE, stderr=PIPE).communicate()
    return not cmd_output_throws_error(flags, response, err, "Compiling core calculus classes failed!")


def rule_calc_gen(flags):
    print "################# Generating calculus rule files ##################"

    if "all" in flags or "isabelle" in flags :

        paths = glob(TEMPLATE_FILES_PATH + '*.thy')
        list = [p.split('/')[1].split('.')[0] for p in paths]
        
        builder = isabuilder.IsabelleBuilder(CALC_TEMPLATE)
        CALC_NAME = builder.get("calc_name")

        builder.add("export_path", nav_to_folder(ISABELLE_SRC_PATH, SCALA_SRC_PATH))
        builder.add("parser_command", "scala -classpath {0}bin Parser".format(OUTPUT_PATH))

        if ISA_RULES_TEMPLATE in list:
            print "Generating calculus rules from", paths[list.index(ISA_RULES_TEMPLATE)], "..."
            
            if not doBuild(builder, paths[list.index(ISA_RULES_TEMPLATE)], OUTPUT_PATH+ISABELLE_SRC_PATH+CALC_NAME+".thy"): return False
            utils.generateIsaROOT(CALC_NAME, OUTPUT_PATH+ISABELLE_SRC_PATH)
            
            print "Compiling Isabelle source files in", OUTPUT_PATH + ISABELLE_SRC_PATH, "..."
            if "force" in flags:
                cmd = "isabelle build -D " + OUTPUT_PATH + ISABELLE_SRC_PATH + " -c"
            else:
                cmd = "isabelle build -D " + OUTPUT_PATH + ISABELLE_SRC_PATH
            response,err = Popen(shlex.split(cmd), stdout=PIPE, stderr=PIPE).communicate()
            if cmd_output_throws_error(flags, response, err, "Generating calculus rules .scala file failed!"): return False

    paths = glob(TEMPLATE_FILES_PATH + '*.scala')
    list = [p.split('/')[-1].split('.')[0] for p in paths]
    builder = scalabuilder.ScalaBuilder(CALC_TEMPLATE)
    builder.add("core_compiled", "")

    if PARSER_TEMPLATE in list:
        print "Rebuilding parser from", paths[list.index(PARSER_TEMPLATE)], "..."
        if not doBuild(builder,paths[list.index(PARSER_TEMPLATE)], OUTPUT_PATH+SCALA_SRC_PATH+PARSER_TEMPLATE+".scala"): return False
        #args = [CALC_TEMPLATE, "parser", paths[list.index(PARSER_TEMPLATE)], OUTPUT_PATH+SCALA_SRC_PATH+PARSER_TEMPLATE+".scala"]
        #cmd = "scala -classpath bin:. CalcGenerator " + " ".join(args)
        #response,err = Popen(shlex.split(cmd), stdout=PIPE).communicate()
        #if cmd_output_throws_error(flags, response, err, "Generating parser class failed!"): return False
        #CALC_NAME = builder.get("calc_name")

    if PRINT_TEMPLATE in list:
        print "Rebuilding print class from", paths[list.index(PRINT_TEMPLATE)], "..."
        if not doBuild(builder,paths[list.index(PRINT_TEMPLATE)], OUTPUT_PATH+SCALA_SRC_PATH+PRINT_TEMPLATE+".scala"): return False

    return True

def add_gui(flags):
    paths = glob(TEMPLATE_FILES_PATH + 'gui/*.scala')
    list = [p.split('/')[-1].split('.')[0] for p in paths]
    builder = scalabuilder.ScalaBuilder(CALC_TEMPLATE)
    builder.add("core_compiled", "")

    if not os.path.exists(OUTPUT_PATH + SCALA_SRC_PATH + "gui/"):
        os.makedirs(OUTPUT_PATH + SCALA_SRC_PATH + "gui/")
    print "Building toobox GUI ..."

    for l in list:
        if not doBuild(builder,paths[list.index(l)], OUTPUT_PATH+SCALA_SRC_PATH+"gui/"+l+".scala"): return False

    if os.path.exists(TEMPLATE_FILES_PATH+"build.py"):
        print "Copying build.py scrtipt ..."
        shutil.copyfile(TEMPLATE_FILES_PATH+"build.py", OUTPUT_PATH+"build.py")
        cmd = "chmod +x " + OUTPUT_PATH+"build.py"
        response,err = Popen(shlex.split(cmd), stdout=PIPE, stderr=PIPE).communicate()

    if os.path.exists(TEMPLATE_FILES_PATH+"Makefile"):
        print "Copying Makefile ..."
        shutil.copyfile(TEMPLATE_FILES_PATH+"Makefile", OUTPUT_PATH+"Makefile")
        cmd = "chmod +x " + OUTPUT_PATH+"Makefile"
        response,err = Popen(shlex.split(cmd), stdout=PIPE, stderr=PIPE).communicate()

    print "Copying libs ..."

    if not os.path.exists(OUTPUT_PATH + "lib/"):
        os.makedirs(OUTPUT_PATH + "lib/")
    libs = glob(LIB_FILES_PATH + '*.jar')
    list = [p.split('/')[-1].split('.')[0] for p in libs]
    print list, libs
    for l in list:
        shutil.copyfile(libs[list.index(l)], OUTPUT_PATH + "lib/"+l+".jar")




def main(argv):
    try:
        opts, args = getopt.getopt(argv, "hfvc:p:t:b:s:", ["help", "force", "verbose", "build=", "calc=", "path=", "template=", "stage="])
    except getopt.GetoptError:
        usage()
        sys.exit(2)

    global OUTPUT_PATH
    global TEMPLATE_FILES_PATH
    global SCALA_SRC_PATH
    global ISABELLE_SRC_PATH
    global CALC_TEMPLATE
    #user flag settings
    BUILD_FLAGS = ["all"]
    STAGE = None

    for opt, arg in opts:
        if opt in ("-h", "--help"):
            usage()
            sys.exit()
        elif opt in ("-c", "--calc"):
            CALC_TEMPLATE = arg
        elif opt in ("-p", "--path"):
            OUTPUT_PATH = arg
        elif opt in ("-t", "--template"):
            TEMPLATE_FILES_PATH = arg
        elif opt in ("-f", "--force"):
            BUILD_FLAGS.append("force")
        elif opt in ("-v", "--verbose"):
            BUILD_FLAGS.append("verbose")
        elif opt in ( "-b", "--build"):
            BUILD_FLAGS.remove("all")
            BUILD_FLAGS += arg.split(",")
        elif opt in ( "-s", "--stage"):
            STAGE = arg
    #sanitize paths
    if not OUTPUT_PATH.endswith('/'):
        OUTPUT_PATH = OUTPUT_PATH + "/"
    if not TEMPLATE_FILES_PATH.endswith('/'):
        TEMPLATE_FILES_PATH = TEMPLATE_FILES_PATH + "/"
    if not SCALA_SRC_PATH.endswith('/'):
        SCALA_SRC_PATH = SCALA_SRC_PATH + "/"
    if not ISABELLE_SRC_PATH.endswith('/'):
        ISABELLE_SRC_PATH = ISABELLE_SRC_PATH + "/"

    # call a single function form defined via the -s flag
    if STAGE: globals()[STAGE](BUILD_FLAGS)
    else:
        #build the core calculus
        if core_calc_gen(BUILD_FLAGS):
            #compile the core calculus
            if calc_compile(BUILD_FLAGS):
                #build the core calculus rules
                if rule_calc_gen(BUILD_FLAGS):
                    #recompile the core calculus (now with rules)
                    if calc_compile(BUILD_FLAGS):
                        add_gui(BUILD_FLAGS)
                        print CALC_NAME, "has been successfully built..."

if __name__ == "__main__":
    main(sys.argv[1:])