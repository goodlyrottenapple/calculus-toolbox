#!/usr/bin/env python

import time, sys, getopt, os
from watchdog.observers import Observer  
from watchdog.events import PatternMatchingEventHandler
from tools import utils


def usage():
    print "This is a watchdog decomiler for calc-toolbox src files"
    usage = ["Usage:"]
    usage.append( "-s  --source    Specify a source folder to be watched" )
    usage.append( "-d  --dest      Specify an output path for decompiled files" )
    usage.append( "-e  --ext       Specify file extensions to be monitored. The default are *.scala and *.thy" )
    usage.append( "-r  --rules     Specify path rewrite rules (currently only hard coded strings, no regex)" )
    usage.append( "-i  --ignore    Specify paths (or substrings of a path) from the source folder to be ignored (currently only hard coded strings, no regex)" )

    print "\n".join(usage)

class MyHandler(PatternMatchingEventHandler):
    source = ""
    destination = ""
    rules = []
    ignore = []
    
    def __init__(self, pat, src, dest, rls, ig):
        PatternMatchingEventHandler.__init__(self)
        patterns = pat
        self.source = src
        self.destination = dest
        self.rules = rls
        self.ignore = ig

        print "Watching for:", patterns, "\nOutput to:", self.destination, "\nIgnoring:", self.ignore

    def process(self, event):
        """
        event.event_type 
            'modified' | 'created' | 'moved' | 'deleted'
        event.is_directory
            True | False
        event.src_path
            path/to/observed/file
        """
        # the file will be processed there
        print event.src_path, event.event_type  # print now only for degug

        for i in self.ignore:
            if i in event.src_path or os.path.isdir(event.src_path):
                print "Ignoring..."
                return

        mod_file = event.src_path.split(self.source)[1]
        for r in self.rules:
            mod_file = mod_file.replace(r[0], r[1])

        print "Writing:", (self.destination + mod_file)
        
        input_file = utils.readFile(event.src_path)

        file_type = mod_file.split(".")[-1]
        reverted = utils.revert( input_file, "(*", "*)" ) if file_type == "thy" else utils.revert( input_file, "/*", "*/" )
        
        if len( reverted ) == 0 and len( input_file ) != 0:
            print "Something might be wrong??"
        else: utils.writeFile( self.destination + mod_file, reverted )


    def on_modified(self, event):
        self.process(event)

    def on_created(self, event):
        self.process(event)

def main(argv):
    try:
        opts, args = getopt.getopt(argv, "hs:d:e:r:i:", ["help", "source=", "dest=", "ext=", "rules=", "ignore="])
    except getopt.GetoptError:
        usage()
        sys.exit(2)

    PATTERNS = ["*.scala", "*.thy"]
    SOURCE = "."
    DEST = ""
    RULES = [("scala/", ""), ("isabelle/", ""), ("DEAK_Core.thy", "Calc_Core.thy"), ("DEAK_Core_SE.thy", "Calc_Core_SE.thy"), ("DEAK.thy", "Calc_Rules.thy"), ("DEAK_SE.thy", "Calc_Rules_SE.thy"), ("DEAK_Eq.thy", "Calc_Eq.thy")]
    IGNORE = ["scala/DEAK.scala", ".thy#", ".thy~", "ROOT"]

    for opt, arg in opts:
        if opt in ("-h", "--help"):
            usage()
            sys.exit()
        elif opt in ("-s", "--source"):
            SOURCE = arg
        elif opt in ("-d", "--dest"):
            DEST = arg
        elif opt in ("-e", "--ext"):
            PATTERNS = ["*."+a.strip() if not a.strip().startswith("*.") else a.strip() for a in arg.split(',')]
            print PATTERNS
        elif opt in ("-r", "--rules"):
            RULES = []
            for a in arg.split(','):
                l = a.split('>')[0].strip()
                r = a.split('>')[1].strip()
                RULES.append((l,r))
            print RULES
            # RULES = arg
        elif opt in ("-i", "--ignore"):
            IGNORE = []
            for a in arg.split(','):
                l = a.strip()
                IGNORE.append(l)
            print IGNORE
            # RULES = arg
       
    if SOURCE.endswith('/') : SOURCE = SOURCE[:-1]
    if DEST.endswith('/') : DEST = DEST[:-1]

    if DEST:
        observer = Observer()
        observer.schedule(MyHandler(PATTERNS, SOURCE, DEST, RULES, IGNORE), path=SOURCE, recursive=True)
        observer.start()

        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            observer.stop()

        observer.join()

if __name__ == "__main__":
    main(sys.argv[1:])
