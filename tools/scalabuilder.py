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

	@staticmethod
	def __ascii_reserved(calc):
		ret = []
		if not isinstance(calc, dict): return []
		for k,v in calc.iteritems():
			if isinstance(v, dict):
				ascii_val = v.get("ascii", "")
				if ascii_val: ret.append(ascii_val)
				ret += ScalaBuilder.__ascii_reserved(v)
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
		return 



#--------------------------------------------------------------------------------------------------------------------------------------------
	
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
				return ScalaBuilder.__is_terminal(type[0], structure) and type[-1] == name
		return False

	@staticmethod
	def __infix_candidtate(name, constructor, structure):
		constructor = structure.get(name, {constructor:{}}).get(constructor, {})
		if constructor:
			type = constructor.get("type", [])
			if len(type) == 3:
				return ScalaBuilder.__is_terminal(type[1], structure) and type[-1] == name and type[0] == name
		return False

	@staticmethod
	def __is_recursive(name, structure):
		#print structure.keys()
		return ScalaBuilder.__is_recursive_aux(name, name, structure)


	@staticmethod
	def __is_recursive_aux(name, current, structure):
		if current not in structure: return False
		else: 
			#print structure[name]
			l = list(set( [ i for c in structure[current].keys() for i in structure[current][c].get("type", [])] ))
			#print(name, current, l)
			if name in l: return True
			if l: 
				return any([ScalaBuilder.__is_recursive_aux(name, i, structure) for i in l if i != current])
			else: return False


	@staticmethod
	def __constructor_parsers_build(name, structure):
		datatype = structure[name]
		sub_parsers_list = []


		for c in datatype:
			if datatype[c].get("parsable", True): #if parsing in ASCII is enabled for this constructor
				#if the constructor is not recursive (ie self referential) or doesnt fit into prefix or infix form....suffix not considered atm
				if name not in datatype[c].get("type", []) or not ScalaBuilder.__prefix_candidtate(name, c, structure) or not ScalaBuilder.__infix_candidtate(name, c, structure):
					constructor = c
					#scala language fix introduced in isabelle -> scala conversion when the datatype and constructor for set datatype are the same
					#ie. datatype Atprop = Atprop *type*, becomes datatype Atprop with constructor Atpropa
					if c == name: constructor += "a"

					def_str = "	lazy val {0}Parser : PackratParser[{1}] =\n		".format(constructor.lower(), name)
					type = datatype[c].get("type", [])

					constructor_with_args = "{0}({1})".format( constructor, ", ".join(ascii_lowercase[:len(type)]) )
					used_parsers_list = ["{0}Parser".format(t.lower()).replace(' ', '_') for t in type]
					tilde_case_list = [ str(x) for x in ascii_lowercase[:len(type)] ]

					#ascii formatting
					
					if "ascii" in datatype[c] and [i for i in datatype[c]["ascii"].split(" ") if i != "_"]:
						filtered_ascii_symb = [i for i in datatype[c]["ascii"].split(" ") if i != "_"][0]
						#print "filtered_ascii_symb: ", filtered_ascii_symb, "\n\n"
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

		#ScalaBuilder.__main_parser_build(name, structure)
		return "\n\n" + ScalaBuilder.__main_parser_build(name, structure) + "\n\n" + "\n\n".join(sub_parsers_list)

	@staticmethod
	def __main_parser_build(name, structure):
		datatype = structure[name]
		prefix_list = []
		infix_list = []

		list_of_generated_parsers = []

		for c in datatype:
			if name in datatype[c].get("type", []) and datatype[c].get("parsable", True):
				print c,"\n"
				if ScalaBuilder.__infix_candidtate(name, c, structure):
					list_of_generated_parsers.append(c)
					print "infix candidate found!!!\n"
					op = datatype[c]["type"][1]
					for cc in structure[op]:
						#print cc, structure[op][cc].get("ascii", c)
						symb = structure[op][cc].get("ascii", c)

						prec = structure[op][cc].get("ascii_precedence", [500, 501])
						prec = ", ".join([str(i) for i in prec])

						#add manual change for precedence!!
						infix = "Infix({3})({0}Parser) {{ (_, a, b) => {1}(a, {2}(), b ) }}".format(cc.lower(), c, cc, prec )
						infix_list.append(infix)
						#print infix

				elif ScalaBuilder.__prefix_candidtate(name, c, structure):
					list_of_generated_parsers.append(c)
					print "prefix candidate found!!!\n"
					op = datatype[c]["type"][0]

					inbetween = [datatype[c]["type"][i] for i in range(1, len(datatype[c]["type"])-1)]

					if inbetween: 
						inbetween_parsers = "~" + "~".join(["{0}Parser".format(t.lower()) for t in inbetween])
						args = "~" + "~".join(ascii_lowercase[:len(inbetween)])
					else: 
						inbetween_parsers = ""
						args = ""


					for cc in structure[op]:
						#print cc, structure[op][cc].get("ascii", c)
						symb = structure[op][cc].get("ascii", c)

						#add manual change for precedence!!
						#Prefix(200)("fboxK" ~ agentParser) { case ("fboxK" ~ a, n)  => Formula_Agent_Formula(Formula_FboxK(), a, n) },

						prec = structure[op][cc].get("ascii_precedence", [200])
						prec = str(prec[0])

						prefix = "Prefix({7})({0}Parser{3}) {{ case (_{4}, {5}) => {1}({2}(){6}, {5}) }}".format(cc.lower(), c, cc, inbetween_parsers, args, ascii_lowercase[len(inbetween)], args.replace('~', ','), prec )
						prefix_list.append(prefix)
						#print prefix

				

		list_of_additional_parsers = []

		#definition for _Parser : PackratParser[_] = ...
		ordered_d = {k : ScalaBuilder.__calc_structure_datatype_constructor_rank(name, k, structure) for k in datatype}

		# fix for rules... the parser for 'rule2' should always be before 'rule' 
		sortedL = sorted(ordered_d, key=ordered_d.get, reverse=False) if "rule" not in name.lower() else sorted(ordered_d.keys(), reverse=True)
		for c in sortedL:
			if c not in list_of_generated_parsers:
				if "ascii" in datatype[c] or "latex" in datatype[c] or "isabelle" in datatype[c]:
					constructor = c
					#scala language fix introduced in isabelle -> scala conversion when the datatype and constructor for set datatype are the same
					#ie. datatype Atprop = Atprop string becomes datatype Atprop with constructor Atpropa
					if c == name: constructor += "a"
				 	list_of_additional_parsers.append( "{0}Parser".format(constructor.lower()) )
					type = datatype[c].get("type", [])
					#if the constructor of current datatype calls another datatype defined in the calulus flag is set to True
					#add_structure introduced for calc_structure_rules which call on calc_structure

		list_of_additional_parsers.append( "\"(\" ~> {0}Parser <~ \")\"".format(name.lower()) )

		ret = "	lazy val {0}Parser:PackratParser[{1}] = operators[Any,{1}](\n		".format(name.lower(), name)
		ret += ",\n		".join([",\n		".join(prefix_list), ",\n		".join(infix_list)])
		ret += "\n	) ( {0} )".format(" | ".join(list_of_additional_parsers))

		ret += "\n\n	def parse{0}(s:String) : Option[{0}] = parseAll({1}Parser,s) match {{\n".format(name, name.lower())
		ret += "		case Success(result, _) => Some(result)\n"
		ret += "		case failure : NoSuccess => None\n"
		ret += "	}"
		return ret



#PARSER-OLD----------------------------------------------------------------------------------------------------------------------------------------

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

#--------------------------------------------------------------------------------------------------------------------------------------------------

	@staticmethod
	def __parse_calc_structure_datatype(name, structure, add_structure={}):
		datatype = structure[name]

		ret = "	lazy val {0}Parser : PackratParser[{1}] = \n		".format(name.lower(), name)
		list_of_parsers = []
		sub_parsers_list = []
		flag = False

		all_ascii_reserved = ScalaBuilder.__ascii_reserved(structure)

		for c in datatype:
			if datatype[c].get("parsable", True):
				constructor = c
				#scala language fix introduced in isabelle -> scala conversion when the datatype and constructor for set datatype are the same
				#ie. datatype Atprop = Atprop *type*, becomes datatype Atprop with constructor Atpropa
				if c == name: constructor += "a"

				def_str = "	lazy val {0}Parser : PackratParser[{1}] =\n		".format(constructor.lower(), name)
				type = datatype[c].get("type", [])

				constructor_with_args = "{0}({1})".format( constructor, ", ".join(ascii_lowercase[:len(type)]) )
				used_parsers_list = ["{0}Parser".format(t.lower()).replace(' ', '_') for t in type]
				tilde_case_list = [ str(x) for x in ascii_lowercase[:len(type)] ]

				#ascii formatting
				
				if "ascii" in datatype[c] and [i for i in datatype[c]["ascii"].split(" ") if i != "_"]:
					filtered_ascii_symb = [i for i in datatype[c]["ascii"].split(" ") if i != "_"][0]

					#this chunk creates an unambiguous parser for acii terminal symbols which are prefixes of other symbols.
					#a terminal  ">" which is a prefix of ">>" and  ">-" will produce a parser - ">" ~ not(">" | "-")
					if len(filtered_ascii_symb) == 1:
						prefixes_of_filtered_ascii = [i.replace('_', ' ').strip() for i in all_ascii_reserved if i.startswith(filtered_ascii_symb[0]) and i != filtered_ascii_symb[0]]
						if prefixes_of_filtered_ascii:
							prefixes_of_filtered_ascii = ["\""+repr(str(i))[len(filtered_ascii_symb[0])+1:-1]+"\"" for i in prefixes_of_filtered_ascii]
							used_parsers_list.insert( datatype[c]["ascii"].split(" ").index(filtered_ascii_symb), "\"{0}\"~not({1})".format( repr(str(filtered_ascii_symb))[1:-1], " | ".join(prefixes_of_filtered_ascii) ) )
						else: used_parsers_list.insert( datatype[c]["ascii"].split(" ").index(filtered_ascii_symb), "\"{0}\"".format( repr(str(filtered_ascii_symb))[1:-1] ) )

					else: used_parsers_list.insert( datatype[c]["ascii"].split(" ").index(filtered_ascii_symb), "\"{0}\"".format( repr(str(filtered_ascii_symb))[1:-1] ) )
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

		# fix for rules... the parser for 'rule2' should always be before 'rule' 
		sortedL = sorted(ordered_d, key=ordered_d.get, reverse=False) if "rule" not in name.lower() else sorted(ordered_d.keys(), reverse=True)
		for c in sortedL:
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

		# if len(datatype) > 1 and flag :
		# now always add a bracketed case
		list_of_parsers.append( "\"(\" ~> {0}Parser <~ \")\"".format(name.lower()) )
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
				if not ScalaBuilder.__is_recursive(d, self.calc["calc_structure"]):
					list.append ( ScalaBuilder.__parse_calc_structure_datatype(d, self.calc["calc_structure"]) )
				else: 
					#list.append ( d+" parser TODO" )
					list.append ( ScalaBuilder.__constructor_parsers_build(d, self.calc["calc_structure"]) )
					#list.append ( d+" parser TODO" )

			ret = "\n" + "\n\n\n\n".join(list) + "\n"
		return ret

#--------------------------------------------------------------------------------------------------------------------------------------------------

	@staticmethod
	def __parser_calc_structure_all_rules(rules):
		ret = "	lazy val ruleParser : PackratParser[Rule] =\n"
		lines = []
		for c in sorted(rules.keys()):
			if c.startswith("Rule"): 
				parser = c.lower()+"Parser"
				lines.append( "		{0} ^^ {{ case a => {1}(a) }}".format(parser, c+'a') )
		lines.append( "		\"Macro\" ~> stringParser ~ prooftreeParser ^^ { case a ~ pt => RuleMacro(a, pt) }" )
		lines.append( "		\"Fail\" ^^ { _ => Fail() }" )
		ret += " |\n".join(lines)

		ret += "\n\n	def parseRule(s:String) : Option[Rule] = parseAll(ruleParser,s) match {\n"
		ret += "		case Success(result, _) => Some(result)\n"
		ret += "		case failure : NoSuccess => None\n"
		ret += "	}"

		return ret


	def parser_calc_structure_rules(self):
		ret = ""
		list = []
		if "calc_structure_rules" in self.calc and "core_compiled" in self.calc:
			for d in sorted(self.calc["calc_structure_rules"].keys()):
				list.append ( ScalaBuilder.__parse_calc_structure_datatype(d, self.calc["calc_structure_rules"], self.calc["calc_structure"]) )
			list.append ( ScalaBuilder.__parser_calc_structure_all_rules(self.calc["calc_structure_rules"]) )
			ret = "\n" + "\n\n\n\n".join(list) + "\n"
		return ret


#--------------------------------------------------------------------------------------------------------------------------------------------------

	@staticmethod
	def __print_calc_structure_datatype(name, structure):
		datatype = structure[name]
		ret = "	def {0}ToString(in:{1}, format:String = LATEX) : String = format match {{\n".format(name.lower(), name)
		isa_list = []
		latex_list = []
		ascii_list = []

		for c in datatype.keys():
			constructor = c if c != name else c +"a" # fix for scala export, as you cant have the same datatype name and constructor
			type = datatype[c].get("type", [])

			args = ",".join(ascii_lowercase[:len(type)])
			x = 0
			type_toString_list = []
			for t in type:
				type_toString_list.append( "{0}ToString({1}, format)".format(t.lower().replace(' ', '_'), ascii_lowercase[ x ]) )
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
			
			# the operator precednece in the isa files is not implemented!! and this might result in warnings
			# if (len(type_toString_list) > 1 or no_sugar) and len([i for i in type_toString_isa_list if not i.startswith("\"")]) > 0: 
			# 	isa_list.append ( "				case {0}({1}) => \"(\" + {2} + \")\"".format(constructor, args, middle) )
			# else : isa_list.append ( "				case {0}({1}) => {2}".format(constructor, args, middle) )
			isa_list.append ( "				case {0}({1}) => \"(\" + {2} + \")\"".format(constructor, args, middle) )

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
			# if "prooftree" in name.lower(): 
			# 	seqs = [i for i in type_toString_list if "sequent" in i]
			# 	pts = [i for i in type_toString_list if "prooftree" in i]
			# 	type_toString_latex_list = pts
			# 	if len(pts) == 1: 
			# 		type_toString_latex_list .append("\"\\\\UnaryInfC{$ \"")
			# 	elif len(pts) == 2: 
			# 		type_toString_latex_list .append("\"\\\\BinaryInfC{$ \"")
			# 	else:
			# 		type_toString_latex_list.append("\"\\\\AxiomC{$ \"")
			# 	type_toString_latex_list += seqs
			# 	type_toString_latex_list.append("\" $}\\n\"")

			# 	middle = " + ".join( type_toString_latex_list )
			# 	latex_list.append ( "				case {0}({1}) => {2}".format(constructor, args, middle) )
			# else:


				# type_toString_list.append( "{0}ToString({1}, format)".format(t.lower().replace(' ', '_'), ascii_lowercase[ x ]) )

			if ScalaBuilder.__prefix_candidtate(name, c, structure):
				type_toString_list[-1] = "bracketIf( {0}, {1}Prec({2}({3}))._2 < {1}Prec({4})._1 )".format( type_toString_list[-1], name.lower(), constructor, args, ascii_lowercase[len(type)-1] )
			elif ScalaBuilder.__infix_candidtate(name, c, structure):
				type_toString_list[0] = "bracketIf( {0}, {1}Prec({2}({3}))._1 <= {1}Prec({4})._1 )".format( type_toString_list[0], name.lower(), constructor, args, ascii_lowercase[0] )
				type_toString_list[-1] = "bracketIf( {0}, {1}Prec({2}({3}))._2 < {1}Prec({4})._1 )".format( type_toString_list[-1], name.lower(), constructor, args, ascii_lowercase[len(type)-1] )


			type_toString_latex_list = list(type_toString_list)
			if "latex" in datatype[c] and [i for i in datatype[c]["latex"].split(" ") if i != "_"]:
				filtered_latex_symbs = [i for i in datatype[c]["latex"].split(" ") if i != "_"]
				for filtered_latex_symb in filtered_latex_symbs:
					type_toString_latex_list.insert(datatype[c]["latex"].split(" ").index(filtered_latex_symb), "\"{0}\"".format( repr(str(filtered_latex_symb))[1:-1] ))
			#else:
			#	type_toString_latex_list.insert(0, "\"{0}\"".format(c))

			if "_Agent_" in c or "_Action_" in c :
				type_toString_latex_list = []
				x = 0
				op = ""
				flag = -1
				for t in type:
					if "op" in t.lower() : 
						op = "{0}ToString({1}, format)".format(t.lower(), ascii_lowercase[ x ])
						type_toString_latex_list.append(  op+".split(\"_\")(0)" )
						flag = x+1
					else: type_toString_latex_list.append( "{0}ToString({1}, format)".format(t.lower(), ascii_lowercase[ x ]) )
							
					if flag == x : 
						type_toString_latex_list.append(  op+".split(\"_\")(1)" )
					
					x += 1

				# duplicated code from above, due to the _Agent_ and _Action_ hackery.....
				if ScalaBuilder.__prefix_candidtate(name, c, structure):
					type_toString_latex_list[-1] = "bracketIf( {0}, {1}Prec({2}({3}))._2 < {1}Prec({4})._1 )".format( type_toString_latex_list[-1], name.lower(), constructor, args, ascii_lowercase[len(type)-1] )
			
					

			middle = " + \" \" + ".join( type_toString_latex_list )
			#if len(type_toString_list) > 1 and len([i for i in type_toString_latex_list if not i.startswith("\"")]) > 0 and "sequent" not in name.lower(): 
			#i feel like the following code is a terrible mess...it basically does magic to remove all but the essential bracketing from a latex term
			# if name in type:
			# 	for c1 in [i for i in datatype.keys() if name in datatype[i]["type"] and len(datatype[i]["type"]) > 2]:
			# 		constructor1 = c1
			# 		if c1 == name: constructor1 += "a" # fix for scala export, as you cant have the same datatype name and constructor
			# 		type1 = datatype[c1].get("type", [])
			# 		args_list = list(ascii_lowercase[0:len(type)])
			# 		args_list[type.index(name)] = "{0}({1})".format(constructor1, ",".join(ascii_lowercase[len(type):len(type)+len(type1)])) 
			# 		args1 = ",".join(args_list)

			# 		type_toString_list = []

			# 		if "_Agent_" in constructor or "_Action_" in constructor :
			# 			x = 0
			# 			flag = -1
			# 			op = ""
			# 			for t in type:
			# 				if "op" in t.lower() : 
			# 					op = "{0}ToString({1}, format)".format(t.lower(), args_list[ x ])
			# 					type_toString_list.append(  op+".split(\"_\")(0)" )
			# 					flag = x+1
			# 				else: type_toString_list.append( "{0}ToString({1}, format)".format(t.lower(), args_list[ x ]) )
							
			# 				if flag == x : 
			# 					type_toString_list.append(  op+".split(\"_\")(1)" )
			# 				x += 1

			# 			if "latex" in datatype[c] and [i for i in datatype[c]["latex"].split(" ") if i != "_"]:
			# 				filtered_latex_symbs = [i for i in datatype[c]["latex"].split(" ") if i != "_"]
			# 				for filtered_latex_symb in filtered_latex_symbs:
			# 					type_toString_list.insert(datatype[c]["latex"].split(" ").index(filtered_latex_symb), "\"{0}\"".format( repr(str(filtered_latex_symb))[1:-1] ))

			# 		else:
			# 			x = 0
			# 			flag = True
			# 			for t in type:
			# 				if t == name and flag : 
			# 					type_toString_list.append( "\"(\" + {0}ToString({1}, format) + \")\"".format(t.lower(), args_list[ x ]) )
			# 					flag = False
			# 				else: type_toString_list.append( "{0}ToString({1}, format)".format(t.lower(), args_list[ x ]) )
			# 				x += 1

			# 			if "latex" in datatype[c] and [i for i in datatype[c]["latex"].split(" ") if i != "_"]:
			# 				filtered_latex_symbs = [i for i in datatype[c]["latex"].split(" ") if i != "_"]
			# 				for filtered_latex_symb in filtered_latex_symbs:
			# 					type_toString_list.insert(datatype[c]["latex"].split(" ").index(filtered_latex_symb), "\"{0}\"".format( repr(str(filtered_latex_symb))[1:-1] ))
			# 		middle1 = " + \" \" + ".join( type_toString_list )
			# 		latex_list.append ( "				case {0}({1}) => {2}".format(constructor, args1, middle1) )
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
	def __print_calc_structure_precedence(name, structure):
		datatype = structure[name]

		ret = "	def {0}Prec(in:{1}) : Tuple2[Int, Int] = in match {{\n".format(name.lower(), name)
		list = []

		for c in datatype:
			constructor = c if c != name else c +"a"

			type = datatype[c].get("type", [])

			args = ",".join(ascii_lowercase[:len(type)])

			
			if ScalaBuilder.__prefix_candidtate(name, c, structure):
				op_type = type[0]
				op_list = []
				for op in structure[op_type]:
					op_constructor = op if op != op_type else op +"a"

					prec = structure[op_type][op].get("ascii_precedence", [200])
					prec = str(prec[0])

					op_list.append("			case {0}() => ({1}, {1})".format(op_constructor, prec))
				list.append( "		case {0}({1}) => a match {{\n{2}\n		}}".format(constructor, args, "\n".join(op_list)) )
			elif ScalaBuilder.__infix_candidtate(name, c, structure):
				op_type = type[1]
				op_list = []
				for op in structure[op_type]:
					op_constructor = op if op != op_type else op +"a"

					prec = structure[op_type][op].get("ascii_precedence", [500, 501])
					prec = ", ".join([str(i) for i in prec])

					op_list.append("			case {0}() => ({1})".format(op_constructor, prec))
				list.append( "		case {0}({1}) => b match {{\n{2}\n		}}".format(constructor, args, "\n".join(op_list)) )
			else: list.append( "		case {0}({1}) => (Int.MinValue, Int.MinValue)".format(constructor, args) )
		
		return ret + "\n".join(list) + "\n	}"
		

	@staticmethod
	def __calc_structure_all_rules(rules):
		ret = "	def ruleToString(in:Rule, format:String = LATEX) : String = format match {\n"
		lines = []
		linesIsa = []
		for c in sorted(rules.keys()):
			if c.startswith("Rule"): 
				lines.append( "             case {0}a(a) => {1}ToString(a, format)".format(c, c.lower()) )
				linesIsa.append( "             case {0}a(a) => \"(\" + \"{0}\" + \" \" + {1}ToString(a, format) + \")\"".format(c, c.lower()) )
		lines.append( "             case RuleMacro(a, pt) => rulemacroToString(a, pt, format)" )
		linesIsa.append( "             case RuleMacro(a, pt) => rulemacroToString(a, pt, format)" )
		ret += "		case ASCII =>\n			in match {\n"
		ret += "\n".join(lines)
		ret += "\n			}\n		case LATEX =>\n			in match {\n"
		ret += "\n".join(lines)
		ret += "\n			}\n		case ISABELLE =>\n			in match {\n"
		ret += "\n".join(linesIsa)
		ret += "\n			}\n	}\n"
		return ret

	def print_calc_structure(self):
		ret = ""
		list = []
		if "calc_structure" in self.calc:
			for d in sorted(self.calc["calc_structure"].keys()):
				list.append ( ScalaBuilder.__print_calc_structure_datatype(d, self.calc["calc_structure"]) )
				if not ScalaBuilder.__is_terminal(d, self.calc["calc_structure"]):
					list.append ( ScalaBuilder.__print_calc_structure_precedence(d, self.calc["calc_structure"]) )
			ret = "\n" + "\n".join(list) + "\n"

		return ret

	def print_calc_structure_rules(self):
		ret = ""
		list = []
		if "calc_structure_rules" in self.calc and "core_compiled" in self.calc: #and flag in self.calc
			for d in sorted(self.calc["calc_structure_rules"].keys()):
				list.append ( ScalaBuilder.__print_calc_structure_datatype(d, self.calc["calc_structure_rules"]) )
			list.append( ScalaBuilder.__calc_structure_all_rules(self.calc["calc_structure_rules"]) )
			ret = "\n" + "\n".join(list) + "\n"

		return ret
