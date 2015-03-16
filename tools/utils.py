#!/usr/bin/env python

import sys, re
from isabuilder import IsabelleBuilder
from scalabuilder import ScalaBuilder

def readFile(file):
	with open(file) as f:
		return f.read()

def processFile(file_str, builder, delimL = "", delimR = ""):
	items = re.findall(re.escape(delimL)+r'[\w+\?]+'+re.escape(delimR), file_str)
	items = list(set(items))
	items_stripped = [s.strip(delimL).strip(delimR) for s in items]

	#prevent from accessing constructor/ static methods
	funs = [i for i in dir(builder) if not i.startswith("_")]
	#print funs
	for i in items_stripped:
		if i.split("?")[0] in funs:
			if len(i.split("?")) == 1:
				str = getattr(builder, i)()
				if str:
					split_index = items[items_stripped.index(i)]
					split = file_str.split(split_index)
					str = delimL + i + "-BEGIN" + delimR + str + delimL + i + "-END" + delimR
					file_str = str.join(split)
			else:
				j = i.split("?")
				str = getattr(builder, j[0])(j[1:])
				if str:
					split_index = items[items_stripped.index(i)]
					#print split_index
					split = file_str.split(split_index)
					str = delimL + i + "-BEGIN" + delimR + str + delimL + i + "-END" + delimR
					file_str = str.join(split)

	return file_str

def writeFile(file, str):
	with open(file, "w") as out:
		out.write(str)

def clean(file_str, delimL = "", delimR = ""):
	items_begin = re.findall(re.escape(delimL)+r'\w+-BEGIN'+re.escape(delimR), file_str)
	items_end = re.findall(re.escape(delimL)+r'\w+-END'+re.escape(delimR), file_str)

	items_beign = list(set(items_begin))
	items_end = list(set(items_end))

	items_begin_stripped = [s.strip(delimL).strip(delimR).strip("-BEGIN") for s in items_beign]
	items_end_stripped = [s.strip(delimL).strip(delimR).strip("-END") for s in items_end]
	for i in items_begin_stripped:
		b = items_beign[items_begin_stripped.index(i)]
		e = items_end[items_end_stripped.index(i)]

		file_str = "".join(["".join(i.split(e)[0:]) for i in file_str.split(b)])

	return file_str

def revert(file_str, delimL = "", delimR = ""):

	#get the sections auto-gen code
	items_begin = re.findall(re.escape(delimL)+r'\w+-BEGIN'+re.escape(delimR), file_str)
	items_end = re.findall(re.escape(delimL)+r'\w+-END'+re.escape(delimR), file_str)

	#remove duplicates
	items_beign = list(set(items_begin))
	items_end = list(set(items_end))

	#strip of comments and '-BEGIN' / '-END'
	items_begin_stripped = [s.strip(delimL).strip(delimR).strip("-BEGIN") for s in items_beign]
	items_end_stripped = [s.strip(delimL).strip(delimR).strip("-END") for s in items_end]
	
	for i in items_begin_stripped:
		b = items_beign[items_begin_stripped.index(i)]
		e = items_end[items_end_stripped.index(i)]

		first = 1
		out = ""
		for j in file_str.split(b):
			if first:
				out += j
				first = not first
			else:
				out += delimL + i + delimR + "".join(j.split(e)[1:])
		file_str = out

	return file_str

def generateIsaROOT(calc_name, out_path):
	str = "session \"out\" = \"HOL\" +\n  options [document = false]\n  theories\n    " + calc_name
	writeFile(out_path+"ROOT", str)

def main(argv):
	isaBuild = IsabelleBuilder("default.json")
	isaBuild.add("export_path", "..")

	isaBuild.add("parser_command", "scala -classpath export/bin Parser")

	scalaBuild = ScalaBuilder("default.json")
	#print getattr(isaBuild, 'calc_name')()
	#print dir(IsabelleBuilder)
	#print isaBuild.get("calc_name")
	#writeFile("export/"+(isaBuild.get("calc_name")+"_Core.thy"), processFile(readFile("template/Calc_Core.thy"), isaBuild, "(*", "*)"))
	writeFile("export/"+(isaBuild.get("calc_name")+".thy"), processFile(readFile("template/Calc.thy"), isaBuild, "(*", "*)"))

	#writeFile("export/Parser.scala", processFile(readFile("template/Parser.scala"), scalaBuild, "/*", "*/"))
	#writeFile("export/Print.scala", processFile(readFile("template/Print.scala"), scalaBuild, "/*", "*/"))

	#writeFile("Calc_Core2.thy", revert(readFile( isaBuild.get("calc_name")+"_Core.thy" )))
#de("EAKMin_Core.thy")
if __name__ == "__main__":
	main(sys.argv[1:])