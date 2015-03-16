#!/usr/bin/env python

import json
from string import ascii_lowercase

class ScalaBuilder:
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
	def add(self, key, val):
		if isinstance(key, basestring): self.calc.update({key:val})

	# return the value for key stored in self.calc dictionary
	def get(self, key):
		return self.calc.get(key, "")

	# returns calc name in the form '{calc_name}'
	# requires calc_name to be defined
	def calc_import(self):
		return "\nimport {0}._\n".format(self.calc.get("calc_name", ""))


	@staticmethod
	def __keywords(calc):
		ret = []
		if not isinstance(calc, dict): return []
		for k in calc:
			ret.append(k)
			if isinstance(calc[k], dict):
				ret += ScalaBuilder.__keywords(calc[k])
		return list(set(ret))

	# uncomments a section enclosed in '(*(*uncommentL?{ident}*) ... (*uncommentR?{ident}*)*)' if 'ident' is defined in 'calc_structure'
	def uncommentL(self, list):
		if len(list) < 1: return ""
		datatypes = ScalaBuilder.__keywords(self.calc)
		if set(list) <= set(datatypes):
			return "*/"
		return ""

	# uncomments a section enclosed in '(*(*uncommentL?{ident}*) ... (*uncommentR?{ident}*)*)' if 'ident' is defined in 'calc_structure'
	def uncommentR(self, list):
		if len(list) < 1: return ""
		datatypes = ScalaBuilder.__keywords(self.calc)
		if set(list) <= set(datatypes):
			return "/*"
		return ""

	@staticmethod
	def __calc_structure_datatype_constructor_rank(name, current, structure):
		type = structure[name][current].get("type", [])
		binding = 1
		if "isabelle" in structure[name][current]: binding += 1
		if not type: return 1.0
		else:
			max_rank = 0.0
			for t in type:
				if t != name:
					rank = (ScalaBuilder.__calc_structure_datatype_rank(t, structure)+1) / float(len(type)) /float(binding)
					if rank > max_rank: max_rank = rank

			return max_rank

	@staticmethod
	def __calc_structure_datatype_rank(name, structure):
		if name not in structure: return 1.0
		max_rank = 0.0
		total_len = 0.0
		for c in structure[name]:
			rank = ScalaBuilder.__calc_structure_datatype_constructor_rank(name, c, structure)
			if rank+1.0 > max_rank:
				max_rank = rank+1.0
			total_len += len(structure[name][c].get("type", []))
		return max_rank

	@staticmethod
	def __parse_calc_structure_datatype(name, structure, add_structure={}):
		datatype = structure[name]

		ret = "	lazy val {0}Parser : PackratParser[{1}] = \n		".format(name.lower(), name)
		list_of_parsers = []
		sub_parsers_list = []
		flag = False

		for c in datatype:
			constructor = c
			#scala language fix introduced in isabelle -> scala conversion when the datatype and constructor for set datatype are the same
			#ie. datatype Atprop = Atprop string becomes datatype Atprop with constructor Atpropa
			if c == name: constructor += "a"

			def_str = "	lazy val {0}Parser : PackratParser[{1}] =\n		".format(constructor.lower(), name)
			type = datatype[c].get("type", [])

			constructor_with_args = "{0}({1})".format( constructor, ", ".join(ascii_lowercase[:len(type)]) )
			used_parsers_list = ["{0}Parser".format(t.lower()) for t in type]
			tilde_case_list = [ str(x) for x in ascii_lowercase[:len(type)] ]

			#ascii formatting
			
			if "ascii" in datatype[c] and [i for i in datatype[c]["ascii"].split(" ") if i != "_"]:
				filtered_ascii_symb = [i for i in datatype[c]["ascii"].split(" ") if i != "_"][0]
				used_parsers_list.insert( datatype[c]["ascii"].split(" ").index(filtered_ascii_symb), "\"{0}\"".format( repr(str(filtered_ascii_symb))[1:-1] ) )
				tilde_case_list.insert( datatype[c]["ascii"].split(" ").index(filtered_ascii_symb), "\"{0}\"".format( repr(str(filtered_ascii_symb))[1:-1] ) )
			elif "type" not in datatype[c]:
				used_parsers_list.insert( 0, "\"{0}\"".format(c) )
				tilde_case_list.insert( 0, "\"{0}\"".format(c) )
			used_parsers = " ~ ".join(used_parsers_list)
			tilde_case = " ~ ".join(tilde_case_list)

			if len(tilde_case_list) == 1 and tilde_case_list[0].startswith("\""):
				sub_parsers_list.append( def_str + "{0} ^^ {{ _ => {1} }}".format(used_parsers, constructor_with_args ) )
			else:
				sub_parsers_list.append( def_str + "{0} ^^ {{ case {1} => {2} }}".format(used_parsers, tilde_case, constructor_with_args ) )


		#definition for _Parser : PackratParser[_] = ...
		ordered_d = {k : ScalaBuilder.__calc_structure_datatype_constructor_rank(name, k, structure) for k in datatype}

		for c in sorted(ordered_d, key=ordered_d.get, reverse=False):
			if "ascii" in datatype[c] or "latex" in datatype[c] or "isabelle" in datatype[c]:
				constructor = c
				#scala language fix introduced in isabelle -> scala conversion when the datatype and constructor for set datatype are the same
				#ie. datatype Atprop = Atprop string becomes datatype Atprop with constructor Atpropa
				if c == name: constructor += "a"
			 	list_of_parsers.append( "{0}Parser".format(constructor.lower()) )
				type = datatype[c].get("type", [])
				#if the constructor of current datatype calls another datatype defined in the calulus flag is set to True
				#add_structure introduced for calc_structure_rules which call on calc_structure
				if type and set(type) <= set(structure.keys()) | set(add_structure.keys()): flag = True

		# add a bracketed case where (expr) is added for each expr that has at least two constructors
		if len(datatype) > 1 and flag : list_of_parsers.append( "\"(\" ~> {0}Parser <~ \")\"".format(name.lower()) )
		ret += " | ".join(list_of_parsers) 

		ret += "\n\n" + "\n\n".join(sub_parsers_list)

		#definition for def parse_(s:String) : Option[_] = parseAll(_Parser,s) match { ...
		ret += "\n\n	def parse{0}(s:String) : Option[{0}] = parseAll({1}Parser,s) match {{\n".format(name, name.lower())
		ret += "		case Success(result, _) => Some(result)\n"
		ret += "		case failure : NoSuccess => None\n"
		ret += "	}"
		return ret

	def parser_calc_structure(self):
		ret = ""
		list = []
		if "calc_structure" in self.calc:
			for d in sorted(self.calc["calc_structure"].keys()):
				list.append ( ScalaBuilder.__parse_calc_structure_datatype(d, self.calc["calc_structure"]) )
			ret = "\n" + "\n\n\n\n".join(list) + "\n"
		return ret

	def parser_calc_structure_rules(self):
		ret = ""
		list = []
		if "calc_structure_rules" in self.calc and "core_compiled" in self.calc:
			for d in sorted(self.calc["calc_structure_rules"].keys()):
				list.append ( ScalaBuilder.__parse_calc_structure_datatype(d, self.calc["calc_structure_rules"], self.calc["calc_structure"]) )
			ret = "\n" + "\n\n\n\n".join(list) + "\n"
		return ret


	@staticmethod
	def __print_calc_structure_datatype(name, datatype):
		ret = "	def {0}ToString(in:{1}, format:String = LATEX) : String = format match {{\n".format(name.lower(), name)
		isa_list = []
		latex_list = []
		ascii_list = []

		for c in datatype.keys():
			constructor = c
			if c == name: constructor += "a" # fix for scala export, as you cant have the same datatype name and constructor
			type = datatype[c].get("type", [])

			args = ",".join(ascii_lowercase[:len(type)])
			x = 0
			type_toString_list = []
			for t in type:
				type_toString_list.append( "{0}ToString({1}, format)".format(t.lower(), ascii_lowercase[ x ]) )
				x += 1

			no_sugar = False
			#isabelle formatting
			type_toString_isa_list = list(type_toString_list)
			if "isabelle" in datatype[c] and [i for i in datatype[c]["isabelle"].split(" ") if i != "_"]:
				filtered_isa_symbs = [i for i in datatype[c]["isabelle"].split(" ") if i != "_"]
				for filtered_isa_symb in filtered_isa_symbs:
					type_toString_isa_list.insert(datatype[c]["isabelle"].split(" ").index(filtered_isa_symb), "\"{0}\"".format( repr(str(filtered_isa_symb))[1:-1] ))
			else:
				type_toString_isa_list.insert(0, "\"{0}\"".format(c))
				no_sugar = True
			middle = " + \" \" + ".join( type_toString_isa_list )
			
			#the operator precednece in the isa files is not implemented!! and this might result in warnings
			if (len(type_toString_list) > 1 or no_sugar) and len([i for i in type_toString_isa_list if not i.startswith("\"")]) > 0: 
				isa_list.append ( "				case {0}({1}) => \"(\" + {2} + \")\"".format(constructor, args, middle) )
			else : isa_list.append ( "				case {0}({1}) => {2}".format(constructor, args, middle) )

			#ascii formatting
			type_toString_ascii_list = list(type_toString_list)
			if "ascii" in datatype[c] and [i for i in datatype[c]["ascii"].split(" ") if i != "_"]:
				filtered_ascii_symbs = [i for i in datatype[c]["ascii"].split(" ") if i != "_"]
				for filtered_ascii_symb in filtered_ascii_symbs:
					type_toString_ascii_list.insert(datatype[c]["ascii"].split(" ").index(filtered_ascii_symb), "\"{0}\"".format( repr(str(filtered_ascii_symb))[1:-1] ))
			#else:
			#	type_toString_ascii_list.insert(0, "\"{0}\"".format(c))
			middle = " + \" \" + ".join( type_toString_ascii_list )
			if len(type_toString_ascii_list) > 1 : ascii_list.append ( "				case {0}({1}) => \"(\" + {2} + \")\"".format(constructor, args, middle) )
			else : ascii_list.append ( "				case {0}({1}) => {2}".format(constructor, args, middle) )

			#latex formatting
			
			#redirect for building latex pt output
			if "prooftree" in name.lower(): 
				seqs = [i for i in type_toString_list if "sequent" in i]
				pts = [i for i in type_toString_list if "prooftree" in i]
				type_toString_latex_list = pts
				if len(pts) == 1: 
					type_toString_latex_list .append("\"\\\\UnaryInfC{$ \"")
				elif len(pts) == 2: 
					type_toString_latex_list .append("\"\\\\BinaryInfC{$ \"")
				else:
					type_toString_latex_list.append("\"\\\\AxiomC{$ \"")
				type_toString_latex_list += seqs
				type_toString_latex_list.append("\" $}\\n\"")

				middle = " + ".join( type_toString_latex_list )
				latex_list.append ( "				case {0}({1}) => {2}".format(constructor, args, middle) )
			else:
				type_toString_latex_list = list(type_toString_list)
				if "latex" in datatype[c] and [i for i in datatype[c]["latex"].split(" ") if i != "_"]:
					filtered_latex_symbs = [i for i in datatype[c]["latex"].split(" ") if i != "_"]
					for filtered_latex_symb in filtered_latex_symbs:
						type_toString_latex_list.insert(datatype[c]["latex"].split(" ").index(filtered_latex_symb), "\"{0}\"".format( repr(str(filtered_latex_symb))[1:-1] ))
				#else:
				#	type_toString_latex_list.insert(0, "\"{0}\"".format(c))
				middle = " + \" \" + ".join( type_toString_latex_list )
				#if len(type_toString_list) > 1 and len([i for i in type_toString_latex_list if not i.startswith("\"")]) > 0 and "sequent" not in name.lower(): 
				#i feel like the following code is a terrible mess...it basically does magic to remove all but the essential bracketing from a latex term
				if name in type:
					for c1 in [i for i in datatype.keys() if name in datatype[i]["type"] and len(datatype[i]["type"]) > 2]:
						constructor1 = c1
						if c1 == name: constructor1 += "a" # fix for scala export, as you cant have the same datatype name and constructor
						type1 = datatype[c1].get("type", [])
						args_list = list(ascii_lowercase[0:len(type)])
						args_list[type.index(name)] = "{0}({1})".format(constructor1, ",".join(ascii_lowercase[len(type):len(type)+len(type1)])) 
						args1 = ",".join(args_list)

						x = 0
						flag = True
						type_toString_list = []
						for t in type:
							if t == name and flag : 
								type_toString_list.append( "\"(\" + {0}ToString({1}, format) + \")\"".format(t.lower(), args_list[ x ]) )
								flag = False
							else: type_toString_list.append( "{0}ToString({1}, format)".format(t.lower(), args_list[ x ]) )
							x += 1

						if "latex" in datatype[c] and [i for i in datatype[c]["latex"].split(" ") if i != "_"]:
							filtered_latex_symbs = [i for i in datatype[c]["latex"].split(" ") if i != "_"]
							for filtered_latex_symb in filtered_latex_symbs:
								type_toString_list.insert(datatype[c]["latex"].split(" ").index(filtered_latex_symb), "\"{0}\"".format( repr(str(filtered_latex_symb))[1:-1] ))
						middle1 = " + \" \" + ".join( type_toString_list )
						latex_list.append ( "				case {0}({1}) => {2}".format(constructor, args1, middle1) )
				latex_list.append ( "				case {0}({1}) => {2}".format(constructor, args, middle) )

		ret += "		case ASCII =>\n			in match {\n"
		ret += "\n".join(ascii_list)
		ret += "\n			}\n		case LATEX =>\n			in match {\n"
		ret += "\n".join(latex_list)
		ret += "\n			}\n		case ISABELLE =>\n			in match {\n"
		ret += "\n".join(isa_list)
		ret += "\n			}\n	}\n"
		return ret

	@staticmethod
	def __calc_structure_all_rules(rules):
		ret = "	def {0}ToString(in:{1}, format:String = LATEX) : String = in match {{\n".format("rule", "Rule")
		lines = []
		for c in sorted(rules.keys()):
			if c.startswith("Rule"): lines.append( "        case {0}a(a) => {1}ToString(a, format)".format(c, c.lower()) )
		return ret + "\n".join(lines) +"\n	}"

	def print_calc_structure(self):
		ret = ""
		list = []
		if "calc_structure" in self.calc:
			for d in sorted(self.calc["calc_structure"].keys()):
				list.append ( ScalaBuilder.__print_calc_structure_datatype(d, self.calc["calc_structure"][d]) )
			ret = "\n" + "\n".join(list) + "\n"

		return ret

	def print_calc_structure_rules(self):
		ret = ""
		list = []
		if "calc_structure_rules" in self.calc and "core_compiled" in self.calc: #and flag in self.calc
			for d in sorted(self.calc["calc_structure_rules"].keys()):
				list.append ( ScalaBuilder.__print_calc_structure_datatype(d, self.calc["calc_structure_rules"][d]) )
			list.append( ScalaBuilder.__calc_structure_all_rules(self.calc["calc_structure_rules"]) )
			ret = "\n" + "\n".join(list) + "\n"

		return ret
