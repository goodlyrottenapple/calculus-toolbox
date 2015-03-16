#!/usr/bin/env python

import json
from string import ascii_lowercase

class IsabelleBuilder:
	# add any macro processing methods to this file. they will automatically be called if referenced in the processed file
	# i.e if a method foo is defined, it will be called if (*foo*) appears in the processed file
	# for passing arguments to foo, use (*foo?arg1?arg2?arg3?etc*)
	# always add '__' before method name if it is going to be static/hidden from direct use


	def __init__(self, file):
		self.calc = {}
		with open(file) as f:
			self.calc = json.loads(f.read())
			for d in self.calc["calc_structure"].keys():
				#normalize type which can either be a string or list of strings
				for c in self.calc["calc_structure"][d].keys():
					if "type" in self.calc["calc_structure"][d][c]:
						type = self.calc["calc_structure"][d][c]["type"]
						if isinstance(type, basestring): type = [type]
						self.calc["calc_structure"][d][c]["type"] = type

	# add a key,value pair to the definition of calculus i.e. set 'export_path'
	# use string as a key otherwise the pair won't be added !!!
	def add(self, key, val):
		if isinstance(key, basestring): self.calc.update({key:val})

	# return the value for key stored in self.calc dictionary
	def get(self, key):
		return self.calc.get(key, "")

	# returns calc name in the form '{calc_name}_Core'
	# requires calc_name to be defined
	def calc_name_core(self):
		if "calc_name" in self.calc: return self.calc["calc_name"]+"_Core"
		return ""

	# returns calc name in the form '{calc_name}'
	# requires calc_name to be defined
	def calc_name(self):
		return self.calc.get("calc_name", "")

	# returns a path of the exported scala file from isabelle in the form '"{export_path}/{calc_name}.scala"'
	# requires calc_name and export_path to be defined
	def export_path(self):
		if {"calc_name", "export_path"} <= set(self.calc.keys()): 
			return "\"{0}{1}.scala\"".format(self.calc["export_path"], self.calc["calc_name"])
		return ""
	
	@staticmethod
	def __keywords(calc):
		ret = []
		if not isinstance(calc, dict): return []
		for k in calc:
			ret.append(k)
			if isinstance(calc[k], dict):
				ret += IsabelleBuilder.__keywords(calc[k])
		return list(set(ret))

	# uncomments a section enclosed in '(*(*uncommentL?{ident}*) ... (*uncommentR?{ident}*)*)' if 'ident' is defined in 'calc_structure'
	def uncommentL(self, list):
		if len(list) < 1: return ""
		datatypes = IsabelleBuilder.__keywords(self.calc)
		if set(list) <= set(datatypes):
			return "*)"
		return ""

	# uncomments a section enclosed in '(*(*uncommentL?{ident}*) ... (*uncommentR?{ident}*)*)' if 'ident' is defined in 'calc_structure'
	def uncommentR(self, list):
		if len(list) < 1: return ""
		datatypes = IsabelleBuilder.__keywords(self.calc)
		if set(list) <= set(datatypes):
			return "(*"
		return ""


	# returns a dictionary of data types declared in 'calc_structure' with their dependencies on the other data structures
	@staticmethod
	def __calc_structure_dependencies(structure):
		dependencies = {}

		for d in structure.keys():
			datatype = structure[d]
			for c in datatype.keys():
				type = datatype[c].get("type", [])
				
				if type:
					old = dependencies.get(d, [])
					dependencies.update({d: list(set(old+[i for i in type if i in structure.keys() and i != d]))})
				
		return dependencies

	# returns a definition of a datatype in isabelle with sugar notation if defined
	@staticmethod
	def __calc_structure_datatype(name, datatype):
		ret = "datatype {0} = ".format(name)
		lines = []
		for c in sorted(datatype.keys()):
			con = datatype[c]
			type = con.get("type",[])

			precedence = con.get("precedence", [])
			if precedence:
				precedence = [str(i) for i in precedence]
				if len(precedence) > 1:
					precedence = " [{0}] {1}".format( ",".join(precedence[:-1]), precedence[-1] )
				else:
					precedence = " {0}".format( precedence[0] )
			else: precedence = ""

			sugar = con.get("isabelle","")
			if sugar:
				if sugar.startswith("("):
					sugar = " " + sugar
				else:
					if sugar.startswith("_") and sugar.endswith("_"): pass
					elif sugar.endswith("_"): sugar = sugar + (" _" * (len(type)-1))
					elif sugar.startswith("_"): sugar = ("_ " * (len(type)-1)) + sugar
					else: sugar = sugar + (" _" * len(type))
					sugar = " (\"{0}\"{1})".format(sugar, precedence)

			if type: type = " " + " ".join(type)
			else: type = ""

			lines.append( "{0}{1}{2}".format(c, type, sugar) )
		return ret + ("\n" + (" " * (len(ret)-2)) + "| ").join(lines)



	def calc_structure(self):
		list = []
		if "calc_structure" in self.calc:
			#print self.calc["calc_structure"]
			structure = self.calc["calc_structure"]

			dependencies = IsabelleBuilder.__calc_structure_dependencies(structure)
			done = sorted(structure.keys())

			while len(done) > 0:
				k = done[0]
				done.remove(k)

				if k not in dependencies.keys():
					#print "adding", k
					list.append ( IsabelleBuilder.__calc_structure_datatype(k, structure[k]) )
					for i in dependencies.keys():
						if k in dependencies[i]: dependencies[i].remove(k)
						if dependencies[i] == [] : del dependencies[i]
					#print dependencies
				else : done.append(k)
		return "\n" + "\n\n".join(list) + "\n"


	@staticmethod
	def __calc_structure_all_rules(rules):
		ret = "datatype Rule = "
		lines = []
		for c in sorted(rules.keys()):
			if c.startswith("Rule"): lines.append( "{0} {0}".format(c) )
		lines.append( "Fail" )
		return ret + ("\n" + (" " * (len(ret)-2)) + "| ").join(lines)

	def __calc_structure_rules_concl(self):
		if "calc_structure_rules" in self.calc and "Prooftree" in self.calc["calc_structure_rules"]:
			ret = "fun concl :: \"Prooftree \<Rightarrow> Sequent\" where\n"
			pt = self.calc["calc_structure_rules"]["Prooftree"]

			lines = []
			for c in sorted(pt.keys()):
				if "isabelle" in pt[c]:

					type = pt[c].get("type", [])

					args = list(ascii_lowercase[:len(type)])
					
					if "isabelle" in pt[c] and [i for i in pt[c]["isabelle"].split(" ") if i != "_"]:
						filtered_isa_symbs = [i for i in pt[c]["isabelle"].split(" ") if i != "_"]
						for filtered_isa_symb in filtered_isa_symbs:
							args.insert(pt[c]["isabelle"].split(" ").index(filtered_isa_symb), "{0}".format( filtered_isa_symb ))

					#x = pt[c]["isabelle"].split("\"")[1].split("\"")[0].strip()[1:]
					x = pt[c].get("type", []).index("Sequent")
					lines.append( "\"concl ({0}) = {1}\"".format( " ".join(args), ascii_lowercase[x] ) )
			return ret + " |\n".join(lines)
		return ""

	def calc_structure_rules(self):
		list = []
		if "calc_structure_rules" in self.calc:
			#print self.calc["calc_structure_rules"]
			rules = self.calc["calc_structure_rules"]

			dependencies = IsabelleBuilder.__calc_structure_dependencies(rules)
			done = sorted(rules.keys())

			while len(done) > 0:
				k = done[0]
				done.remove(k)

				if k not in dependencies.keys():
					#print "adding", k
					list.append ( IsabelleBuilder.__calc_structure_datatype(k, rules[k]) )
					for i in dependencies.keys():
						if k in dependencies[i]: dependencies[i].remove(k)
						if dependencies[i] == [] : del dependencies[i]
					#print dependencies
				else : done.append(k)
		list.append ( IsabelleBuilder.__calc_structure_all_rules(rules) )
		list.append ( self.__calc_structure_rules_concl() )

		return "\n" + "\n\n".join(list) + "\n"

	@staticmethod
	def __calc_structure_rules_rule_list_aux(name, rules, parser_command):
		import shlex
		from subprocess import Popen, PIPE

		l = [i for r in rules for i in rules[r]]
		cmd = parser_command + " '{0}'".format(json.dumps(l))
		response, err = Popen(shlex.split(cmd), stdout=PIPE).communicate()
		response_list = json.loads(response)

		ret = []
		if len(response_list) == len(l):
			index = 0
			for r in rules:
				count = 0
				r_str = ""
				r_list = []
				for i in rules[r]:
					if count == 0: r_str += "\"rule ({0} {0}.{1}) = {2} \<Longrightarrow>RD ".format(name, r, response_list[index])
					else: r_list.append( response_list[index] )
					index += 1
					count += 1
				r_str += "[{0}]\"".format(",".join(r_list))
				ret.append(r_str)
			return " |\n".join(ret)
		else: return ""
		
	def rules_rule_fun(self):
		if "parser_command" in self.calc and "rules" in self.calc:
			ret = []
			for r in sorted(self.calc["rules"]):
				ret.append( IsabelleBuilder.__calc_structure_rules_rule_list_aux(r, self.calc["rules"][r], self.calc["parser_command"]) )
			return "\n" + "| \n".join(ret) + "|\n"
		return ""

	def rules_rule_list(self):
		if "parser_command" in self.calc and "rules" in self.calc:
			ret = []
			for r in sorted(self.calc["rules"]):
				ret.append( "(map ({0}) [{1}])".format(r, ",".join(self.calc["rules"][r].keys())) )
			return " @ ".join(ret)
		return ""

