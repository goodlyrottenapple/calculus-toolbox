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
		return self.calc.get("calc_name", "")+"_Core"

	def calc_name_core_se(self):
		return self.calc.get("calc_name", "")+"_Core_SE"

	# returns calc name in the form '{calc_name}'
	# requires calc_name to be defined
	def calc_name(self):
		return self.calc.get("calc_name", "")

	def calc_name_se(self):
		return self.calc.get("calc_name", "")+"_SE"

	def calc_name_eq(self):
		return self.calc.get("calc_name", "")+"_Eq"

	# returns a path of the exported scala file from isabelle in the form '"{export_path}/{calc_name}.scala"'
	# requires calc_name and export_path to be defined
	def export_path(self):
		if {"calc_name", "export_path"} <= set(self.calc.keys()): 
			return "\"{0}{1}.scala\"".format(self.calc["export_path"], self.calc["calc_name"])
		return ""
	
	# given a calculus dictionary, recursively returns all the keys of the dictionary and any subdictionaries
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






	@staticmethod
	def __is_terminal(name, structure):

		l = [ i for c in structure.get(name, {}).keys() for i in structure.get(name, {}).get(c, {}).get("type", []) ]
		# print name, structure.get(name, {}).keys()
		if l: return False
		return True

	@staticmethod
	def __prefix_candidtate(name, constructor, structure):
		constructor = structure.get(name, {}).get(constructor, {})
		if constructor:
			type = constructor.get("type", [])
			if type:
				return IsabelleBuilder.__is_terminal(type[0], structure) and type[-1] == name
		return False

	@staticmethod
	def __infix_candidtate(name, constructor, structure):
		constructor = structure.get(name, {constructor:{}}).get(constructor, {})
		if constructor:
			type = constructor.get("type", [])
			if len(type) == 3:
				return IsabelleBuilder.__is_terminal(type[1], structure) and type[-1] == name and type[0] == name
		return False

	@staticmethod
	def __is_recursive(name, structure):
		#print structure.keys()
		return IsabelleBuilder.__is_recursive_aux(name, name, structure)


	@staticmethod
	def __is_recursive_aux(name, current, structure):
		if current not in structure: return False
		else: 
			#print structure[name]
			l = list(set( [ i for c in structure[current].keys() for i in structure[current][c].get("type", [])] ))
			#print(name, current, l)
			if name in l: return True
			if l: 
				return any([IsabelleBuilder.__is_recursive_aux(name, i, structure) for i in l if i != current])
			else: return False







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
	def __calc_structure_datatype(name, datatype, structure, shallow = False):
		if shallow:
			if IsabelleBuilder.__is_terminal(name, structure): return ""

			constructors = [k for k in datatype.keys() if datatype[k].get("shallow", True)]

			# case of Atprop being redundant in SE as a datatype, instead use type_synonym
			if len(constructors) == 1:
				type = datatype[constructors[0]].get("type", [])
				if len(type)== 1 and not set(structure.keys()) & set(type):
					return "type_synonym {0} = {1}".format(name, type[0])


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
			# print precedence

			sugar = con.get("isabelle","")
			if sugar:
				if sugar.startswith("("):
					sugar = " " + sugar
				else:
					if sugar.startswith("_") and sugar.endswith("_"): pass
					elif sugar.endswith("_"): sugar = sugar + (" _" * (len(type)-1))
					elif sugar.startswith("_"): sugar = ("_ " * (len(type)-1)) + sugar
					else: sugar = sugar + (" _" * len(type))



			if shallow and IsabelleBuilder.__prefix_candidtate(name, c, structure):
				for cc in structure[type[0]]:

					precedence = con.get("precedence", [])
					if precedence:
						precedence = [str(i) for i in precedence]
						if len(precedence) > 1:
							precedence = " [{0}] {1}".format( ",".join(precedence[1:-1]), precedence[-1] )
						else:
							precedence = " {0}".format( precedence[0] )
					else: precedence = ""

					sugar_c = structure[type[0]][cc].get("isabelle","")
					if sugar_c and sugar:
						sugar_t = sugar.split(" ")
						sugar_t = sugar_t[1:]
						sugar_t[0] = sugar_c
						sugar_t = " (\"{0}\"{1})".format(" ".join(sugar_t), precedence)
					else: sugar_t = ""

					lines.append( "{0} {1}{2}".format(cc, " ".join(type[1:]), sugar_t) )

			elif shallow and IsabelleBuilder.__infix_candidtate(name, c, structure):
				for cc in structure[type[1]]:
					precedence = con.get("precedence", [])
					if precedence: precedence = str(precedence[0])
					else: precedence = "400"

					sugar = structure[type[1]][cc].get("isabelle","")
					if sugar: sugar = "(infix \"{0}\" {1})".format(sugar, precedence)
					else: sugar = ""
					lines.append( "{0} {1} {2} {3}".format(cc , type[0], type[2], sugar) )

			elif shallow and len(type) == 1 and IsabelleBuilder.__is_terminal(type[0], structure) and structure.get(type[0], {}):
				for cc in structure[type[0]]:
					sugar = structure[type[0]][cc].get("isabelle", "")
					lines.append( "{0} (\"{1}\")".format(cc,sugar, precedence) )

			elif not shallow or datatype[c].get("shallow", True):
				for x in range(len(type)):
					if len(type[x].split(' ')) > 1: type[x] = '\"' + type[x] + '\"'

				if type: type = " " + " ".join(type)
				else: type = ""

				if sugar: sugar = " (\"{0}\"{1})".format(sugar, precedence)

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
					list.append ( IsabelleBuilder.__calc_structure_datatype(k, structure[k], structure) )
					for i in dependencies.keys():
						if k in dependencies[i]: dependencies[i].remove(k)
						if dependencies[i] == [] : del dependencies[i]
					#print dependencies
				else : done.append(k)
		return "\n" + "\n\n".join(list) + "\n"


	def calc_structure_se(self):
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
					ret = IsabelleBuilder.__calc_structure_datatype(k, structure[k], structure, True)
					if ret: list.append ( ret )
					for i in dependencies.keys():
						if k in dependencies[i]: dependencies[i].remove(k)
						if dependencies[i] == [] : del dependencies[i]
					#print dependencies
				else : done.append(k)
		return "\n" + "\n\n".join(list) + "\n"

	@staticmethod
	def __calc_structure_se_to_de(name, datatype, structure, calc_name):
		if IsabelleBuilder.__is_terminal(name, structure): return ""

		ret = "fun SE_to_DE_{0} :: \"{0} \\<Rightarrow> {1}_Core.{0}\" where\n".format(name, calc_name)


		constructors = [k for k in datatype.keys() if datatype[k].get("shallow", True)]

		# case of Atprop being redundant in SE as a datatype, instead use type_synonym
		if len(constructors) == 1:
			type = datatype[constructors[0]].get("type", [])
			if len(type)== 1 and not set(structure.keys()) & set(type):
				return ret + "\"SE_to_DE_{0} x = {0} x\"".format(name)


		# return ret
		lines = []
		for c in sorted(datatype.keys()):
			con = datatype[c]
			type = con.get("type",[])

			if datatype[c].get("shallow", True):

				if IsabelleBuilder.__prefix_candidtate(name, c, structure):
					for cc in structure[type[0]]:
						c_in = ascii_lowercase[1:len(type)]
						c_in = cc + " " + " ".join(c_in)
						c_out = []
						count = 0
						for t in type:
							if count == 0:
								c_out.append( "{1}_Core.{0}".format(cc, calc_name) )
							else:
								c_out.append( "(SE_to_DE_{0} {1})".format(t, ascii_lowercase[count] ) )
							count += 1
						c_out = " ".join( c_out )

						lines.append( "\"SE_to_DE_{0} ({1}) = {4}_Core.{3} {2}\"".format(name, c_in, c_out, c, calc_name) )

					

				elif IsabelleBuilder.__infix_candidtate(name, c, structure):
					for cc in structure[type[1]]:
						c_in = ascii_lowercase[0] + ascii_lowercase[2:len(type)]
						c_in = cc + " " + " ".join(c_in)
						c_out = []
						count = 0
						for t in type:
							if count == 1:
								c_out.append( "{1}_Core.{0}".format(cc, calc_name) )
							else:
								c_out.append( "(SE_to_DE_{0} {1})".format(t, ascii_lowercase[count] ) )
							count += 1
						c_out = " ".join( c_out )

						lines.append( "\"SE_to_DE_{0} ({1}) = {4}_Core.{3} {2}\"".format(name, c_in, c_out, c, calc_name) )


				elif len(type) == 1 and IsabelleBuilder.__is_terminal(type[0], structure) and structure.get(type[0], {}):
					for cc in structure[type[0]]:
						lines.append( "\"SE_to_DE_{0} {1} = {3}_Core.{2} {3}_Core.{1}\"".format(name, cc, c, calc_name) )

				elif len(type) == 1 and IsabelleBuilder.__is_terminal(type[0], structure) and type[0].replace('\"', '').endswith("list") :
					lines.append( "\"SE_to_DE_{0} ({1} list) = {2}_Core.{1} (map (SE_to_DE_{0}) list)\"".format(name, c, calc_name) )

				else:
					c_in = c + " " + " ".join(ascii_lowercase[:len(type)])
					c_out = []
					count = 0
					for t in type:
						c_out.append( "(SE_to_DE_{0} {1})".format(t, ascii_lowercase[count] ) )
						count += 1
					c_out = c + " " + " ".join(c_out)

					lines.append( "\"SE_to_DE_{0} ({1}) = {3}_Core.{2}\"".format(name, c_in, c_out, calc_name) )
		return ret+" |\n".join(lines)


	@staticmethod
	def __case_encapsulate(arg, case, bod, alt):
		return "(case {0} of {1} \\<Rightarrow> {2} | _ \\<Rightarrow> {3})".format(arg, case, bod, alt)

	@staticmethod
	def __case_encapsulate_option(arg, case, bod):
		return IsabelleBuilder.__case_encapsulate(arg, "Some "+case, bod, "None")

	@staticmethod
	def __calc_structure_de_to_se(name, datatype, structure, calc_name):
		if IsabelleBuilder.__is_terminal(name, structure): return ""

		ret = "fun DE_to_SE_{0} :: \"{1}_Core.{0} \\<Rightarrow> {0} option\" where\n".format(name, calc_name)

		constructors = [k for k in datatype.keys() if datatype[k].get("shallow", True)]

		# case of Atprop being redundant in SE as a datatype, instead use type_synonym
		if len(constructors) == 1:
			type = datatype[constructors[0]].get("type", [])
			if len(type)== 1 and not set(structure.keys()) & set(type):
				return ret + "\"DE_to_SE_{0} ({0} x) = Some x\" |\n\"DE_to_SE_{0} _ = None\"".format(name)


		# return ret
		lines = []
		flag = False
		for c in sorted(datatype.keys()):
			con = datatype[c]
			type = con.get("type",[])

			if datatype[c].get("shallow", True):

				if IsabelleBuilder.__prefix_candidtate(name, c, structure):
					for cc in structure[type[0]]:
						c_in = ascii_lowercase[1:len(type)]
						c_out = "Some ({0} {1})".format(cc, " ".join([i+i for i in c_in]))
						c_in = "{2}_Core.{0} {2}_Core.{1} ".format(c, cc, calc_name) + " ".join(c_in)

						count = 0
						for t in type:
							if count != 0:
								c_out = IsabelleBuilder.__case_encapsulate_option("(DE_to_SE_{0} {1})".format(t, ascii_lowercase[count]), ascii_lowercase[count]+ascii_lowercase[count], c_out)
							count += 1

						lines.append( "\"DE_to_SE_{0} ({1}) = {2}\"".format(name, c_in, c_out, cc, calc_name) )


				elif IsabelleBuilder.__infix_candidtate(name, c, structure):
					for cc in structure[type[1]]:
						c_in = ascii_lowercase[0] + ascii_lowercase[2:len(type)]
						c_out = "Some ({0} {1})".format(cc, " ".join([i+i for i in c_in]))
						c_in = "{1}_Core.{0} ".format(c, calc_name) + c_in[0] + " {1}_Core.{0} ".format(cc, calc_name) + " ".join(c_in[1:])

						count = 0
						for t in type:
							if count != 1:
								c_out = IsabelleBuilder.__case_encapsulate_option("(DE_to_SE_{0} {1})".format(t, ascii_lowercase[count]), ascii_lowercase[count]+ascii_lowercase[count], c_out)
							count += 1

						lines.append( "\"DE_to_SE_{0} ({1}) = {2}\"".format(name, c_in, c_out) )


				elif len(type) == 1 and IsabelleBuilder.__is_terminal(type[0], structure) and structure.get(type[0], {}):
					for cc in structure.get(type[0], {}):
						lines.append( "\"DE_to_SE_{0} ({3}_Core.{2} {3}_Core.{1}) = Some {1}\"".format(name, cc, c, calc_name) )

				elif len(type) == 1 and IsabelleBuilder.__is_terminal(type[0], structure) and type[0].replace('\"', '').endswith("list") :
					lines.append( "\"DE_to_SE_{0} ({2}_Core.{1} []) = Some ({1} [])\"".format(name, c, calc_name) )
					lines.append( "\"DE_to_SE_{0} ({2}_Core.{1} (x#xs)) = (case (DE_to_SE_{0} x) of Some res \<Rightarrow> (case (DE_to_SE_{0} ({2}_Core.{1} xs)) of Some ({1} list) \<Rightarrow> Some ({1} (res#list)) | _ \<Rightarrow> None) | _ \<Rightarrow> None )\"".format(name, c, calc_name) )

				else:
					c_in = "{1}_Core.{0} ".format(c, calc_name) + " ".join(ascii_lowercase[:len(type)])
					c_out = "Some ({0} {1})".format(c, " ".join([i+i for i in ascii_lowercase[:len(type)]]))

					count = 0
					for t in type:
						c_out = IsabelleBuilder.__case_encapsulate_option("(DE_to_SE_{0} {1})".format(t, ascii_lowercase[count]), ascii_lowercase[count]+ascii_lowercase[count], c_out)
						count += 1

					lines.append( "\"DE_to_SE_{0} ({1}) = {2}\"".format(name, c_in, c_out) )

			else : 
				flag = True



		if flag: lines.append("\"DE_to_SE_{0} _ = None\"".format(name))

		return ret+" |\n".join(lines)


	def __calc_structure_translate(self, se_to_de = True):
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
					if (se_to_de): ret = IsabelleBuilder.__calc_structure_se_to_de(k, structure[k], structure, self.calc["calc_name"])
					else: ret = IsabelleBuilder.__calc_structure_de_to_se(k, structure[k], structure, self.calc["calc_name"])
					if ret: list.append ( ret )
					for i in dependencies.keys():
						if k in dependencies[i]: dependencies[i].remove(k)
						if dependencies[i] == [] : del dependencies[i]
					#print dependencies
				else : done.append(k)
		return "\n" + "\n\n".join(list) + "\n"

	def calc_structure_se_to_de(self):
		return self.__calc_structure_translate()
	def calc_structure_de_to_se(self):
		return self.__calc_structure_translate(False)

	# generates the definition of datatype Rules
	@staticmethod
	def __calc_structure_all_rules(rules):
		ret = "datatype Rule = "
		lines = []
		for c in sorted(rules.keys()):
			if c.startswith("Rule"): lines.append( "{0} {0}".format(c) )
		# new macro rule
		lines.append( "RuleMacro string Prooftree" )
		lines.append( "Fail" )
		space = (" " * (len(ret)-2))
		return ret + ("\n" + space + "| ").join(lines) + "\n     and Prooftree = Prooftree Sequent Rule \"Prooftree list\" (\"_ \\<Longleftarrow> PT ( _ ) _\" [341,341] 350)"
	
	# deprecated
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
					list.append ( IsabelleBuilder.__calc_structure_datatype(k, rules[k], rules) )
					for i in dependencies.keys():
						if k in dependencies[i]: dependencies[i].remove(k)
						if dependencies[i] == [] : del dependencies[i]
					#print dependencies
				else : done.append(k)
		list.append ( IsabelleBuilder.__calc_structure_all_rules(rules) )
		# list.append ( self.__calc_structure_rules_concl() )

		return "\n" + "\n\n".join(list) + "\n"
	# given a parser command, will pass a list of ASCII rule encodings and expect a JSON list of Isabelle encoded rules
	# generates "primrec ruleBin/Op/etc"
	@staticmethod
	def __calc_structure_rules_rule_list_aux(name, rules, rule_def, parser_command):
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
				premise_added = False
				count = 0
				r_str = ""
				r_list = []
				locale = "({0})".format(rule_def[r]["locale"]) if "locale" in rule_def[r] else "_"
				for i in rules[r]:
					if count == 0:
						r_str += "\"rule{0} x {0}.{1} = ".format(name, r)
						if "locale" in rule_def[r]: 
							r_str += "( case x of {0} \\<Rightarrow>".format(locale)
						elif "condition" in rule_def[r]: r_str += "( "
						if "condition" in rule_def[r]: 
							r_str += "{0} \<Longrightarrow>C {1} \<Longrightarrow>RD ".format(rule_def[r]["condition"], response_list[index])
						else: r_str += "{0} \<Longrightarrow>RD ".format(response_list[index])
					if "premise" in rule_def[r] and not premise_added:
						r_str += rule_def[r]["premise"]
						premise_added = True
					elif count > 0: r_list.append( response_list[index] )
					index += 1
					count += 1
				if "premise" not in rule_def[r]: r_str += "(\\<lambda>x. Some [{0}])".format(",".join(r_list))
				if "locale" in rule_def[r]: r_str += " | _ \\<Rightarrow> ((?\\<^sub>S''X'') \\<turnstile>\\<^sub>S (?\\<^sub>S''Y'')) \\<Longrightarrow>RD (\\<lambda>x. None) )\""
				elif "condition" in rule_def[r]: r_str += " )\""
				else : r_str += "\""
				ret.append(r_str)
			for r in list(set(rule_def.keys()) - set(rules.keys())):
				if "premise" in rule_def[r]: ret.append( "\"rule{0} x {0}.{1} = ((?\\<^sub>S''X'') \\<turnstile>\\<^sub>S (?\\<^sub>S''Y'')) \\<Longrightarrow>RD {2}\"".format(name, r, rule_def[r]["premise"]) )
				else: ret.append( "\"rule{0} x {0}.{1} = ((?\\<^sub>S''X'') \\<turnstile>\\<^sub>S (?\\<^sub>S''Y'')) \\<Longrightarrow>RD (\\<lambda>x. None)\"".format(name, r) )
			return "primrec rule{0} :: \"Locale \<Rightarrow> {0} \<Rightarrow> ruleder\" where\n".format(name) + " |\n".join(ret) + '\n'
		else: return ""



	@staticmethod
	def __calc_structure_rules_se_rule_list_aux(name, rules, rule_def, parser_command):
		import shlex
		from subprocess import Popen, PIPE

		l = [i for r in rules for i in reversed(rules[r])]
		cmd = parser_command + " se '{0}'".format(json.dumps(l))
		response, err = Popen(shlex.split(cmd), stdout=PIPE).communicate()
		response_list = json.loads(response)

		ret = []
		if len(response_list) == len(l):
			index = 0
			for r in rules:
				premise_added = False
				r_list = []
				r_str = ""
				locale = ""
				condition = ""

				if "locale" in rule_def[r]: 
					locale = "({0}) \\<in> set l \\<Longrightarrow> ".format(rule_def[r]["locale"])

				if "condition" in rule_def[r]:
					condition = "{0} seq \\<Longrightarrow> l \\<turnstile>d seq".format(rule_def[r]["condition"])

				for i in rules[r]:											
					if response_list[index]: r_list.append( "l \<turnstile>d " + response_list[index] )
					index += 1

				if "se_rule" in rule_def[r]: 
					condition = ""
					r_str = rule_def[r].get("se_rule", "")
				elif not condition: r_str = " \\<Longrightarrow> ".join(r_list)


				if rule_def[r].get("se", True): ret.append( "{0}: \"{1}{2}{3}\"".format(r, locale, condition, r_str) )
			# for r in list(set(rule_def.keys()) - set(rules.keys())):
			# 	if "premise" in rule_def[r]: ret.append( "\"rule{0} x {0}.{1} = ((?\\<^sub>S''X'') \\<turnstile>\\<^sub>S (?\\<^sub>S''Y'')) \\<Longrightarrow>RD {2}\"".format(name, r, rule_def[r]["premise"]) )
			# 	else: ret.append( "\"rule{0} x {0}.{1} = ((?\\<^sub>S''X'') \\<turnstile>\\<^sub>S (?\\<^sub>S''Y'')) \\<Longrightarrow>RD (\\<lambda>x. None)\"".format(name, r) )
			for r in list(set(rule_def.keys()) - set(rules.keys())):
				r_str = ""
				if "se_rule" in rule_def[r]: 
					r_str = rule_def[r].get("se_rule", "")
				if rule_def[r].get("se", True): ret.append( "{0}: \"{1}\"".format(r, r_str) )

			return "|\n".join(ret) + '\n'
		else: return ""
	# generates a universal rule function that brings all the separate ruleBin/Op/etc functions under one call...	
	def rules_rule_fun(self):
		if "parser_command" in self.calc and "rules" in self.calc:
			ret = []
			rules = []
			for r in sorted(self.calc["rules"]):
				rules.append( "\"rule l ({0} r) = rule{0} l r\"".format(r) )
				ret.append( IsabelleBuilder.__calc_structure_rules_rule_list_aux(r, self.calc["rules"][r], self.calc["calc_structure_rules"][r], self.calc["parser_command"]) )
			#return "\n" + "\n".join(ret) #+ "|\n"
			rules.append( "\"rule _ _ = ((?\\<^sub>S''X'') \\<turnstile>\\<^sub>S (?\\<^sub>S''Y'')) \\<Longrightarrow>RD (\\<lambda>x. None)\"" )

			return '\n' + "\n".join(ret) + "\nfun rule :: \"Locale \<Rightarrow> Rule \<Rightarrow> ruleder\" where\n" + " |\n".join(rules) + '\n'  
		return ""
	# generates the ruleList definition (used for proofsearch in scala, as any rules not in this list will be ommited from the search)
	def rules_rule_list(self):
		if "parser_command" in self.calc and "calc_structure_rules" in self.calc:
			ret = []
			for r in sorted(self.calc["calc_structure_rules"]):
				rules = [rr for rr in self.calc["calc_structure_rules"][r].keys() if rr in self.calc["rules"][r].keys() or "premise" in self.calc["calc_structure_rules"][r][rr] ]
				if len(rules) > 0: ret.append( "(map ({0}) [{1}])".format( r, ",".join(rules) ) )
			return " @ ".join(ret)
		return ""




	def calc_structure_rules_se(self):
		if "parser_command" in self.calc and "rules" in self.calc:
			ret = []
			rules = []
			for r in sorted(self.calc["rules"]):
				# print r
				ret.append( IsabelleBuilder.__calc_structure_rules_se_rule_list_aux(r, self.calc["rules"][r], self.calc["calc_structure_rules"][r], self.calc["parser_command"]) )
			return "\ninductive derivable :: \"Locale list \\<Rightarrow> Sequent \\<Rightarrow> bool\"  (infix \"\\<turnstile>d\" 300) where\n" + "| \n".join(ret) #+ "|\n"

		return ""


	@staticmethod
	def __SE_to_DE_Empty_lemma_aux(name, rules, rule_def, parser_command):
		import shlex
		from subprocess import Popen, PIPE

		l = [i for r in rules for i in rules[r]]
		cmd = parser_command + " se '{0}'".format(json.dumps(l))
		response, err = Popen(shlex.split(cmd), stdout=PIPE).communicate()
		response_list = json.loads(response)

		ret = []
		if len(response_list) == len(l):
			index = 0
			for r in rules:
				premise_added = False
				r_list = []
				r_str = ""
				locale = ""
				concl = ""
				prem_list = []

				count = 0

				for i in rules[r]:											
					if count == 0: concl = response_list[index]
					else: prem_list.append( "\"DE_to_SE_Sequent (concl {1}{1}) = Some ({0}) \\<and> isProofTreeWoMacro [DEAK.Locale.Empty] {1}{1}\"".format(response_list[index], ascii_lowercase[count-1]) )
					index += 1
					count += 1


				if "locale" in rule_def[r]: 
					r_str = "case {0} thus ?case by simp\n".format(r)
					r_str += "next"
					ret.append( r_str )


				else:
					count = len(rules[r])
					search_str = ""
					for i in reversed(rules[r]):
						# print i
						if count > 1: search_str+=i
						count -= 1
					import re
					params = re.findall("\?\w", search_str)
					params = [i.replace('?', '') for i in params]
					r_str = "case ({0} {1})\n".format(r, " ".join(params))
					r_str += "  then obtain {2} where assms: {1} by auto\n".format( concl, " ".join(prem_list), " ".join([i+i for i in ascii_lowercase[:len(prem_list)]]) )
					r_str += "  show ?case\n"
					r_str += "  apply (se_to_de_tac \"(SE_to_DE_Sequent ({2})) \\<Longleftarrow>PT ({0} {1}) [{3}]\" add: assms)\n".format( name, r, concl, ", ".join([i+i for i in ascii_lowercase[:len(prem_list)]]) )
  					r_str += "  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+\n"
  					# r_str += "  using DS_SD_Sequent_Id assms isProofTree_concl_freevars by fastforce+\n"
					r_str += "next"
					# ret.append( r_str )
			for r in list(set(rule_def.keys()) - set(rules.keys())):

				import re
				params = re.findall("\?\w", search_str)
				params = [i.replace('?', '') for i in params]
				r_str = "case ({0} {1})\n".format(r, " ".join(params))
				r_str += "  then obtain {2} where assms: {1} by auto\n".format( concl, " ".join(prem_list), " ".join([i+i for i in ascii_lowercase[:len(prem_list)]]) )
				r_str += "  show ?case\n"
				r_str += "  apply (se_to_de_tac \"(SE_to_DE_Sequent ({2})) \\<Longleftarrow>PT ({0} {1}) [{3}]\" add: assms)\n".format( name, r, concl, ", ".join([i+i for i in ascii_lowercase[:len(prem_list)]]) )
				r_str += "  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+\n"
					# r_str += "  using DS_SD_Sequent_Id assms isProofTree_concl_freevars by fastforce+\n"
				r_str += "next"
				ret.append( r_str )

			return "\n".join(ret) + '\n'
		else: return ""


	def SE_to_DE_Empty_lemma(self):
		if "parser_command" in self.calc and "rules" in self.calc:
			ret = []
			rules = []
			for r in sorted(self.calc["rules"]):
				# print r
				ret.append( IsabelleBuilder.__SE_to_DE_Empty_lemma_aux(r, self.calc["rules"][r], self.calc["calc_structure_rules"][r], self.calc["parser_command"]) )
			return "\n" + "\n".join(ret)

		return ""


