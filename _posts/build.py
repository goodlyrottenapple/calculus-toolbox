#!/usr/bin/env python
# -*- coding: utf-8 -*-
import os,sys,re,getopt,shlex, shutil
from subprocess import Popen, PIPE
from glob import glob

TEX_CONST = r"""\documentclass[]{article}
\usepackage{lmodern}
\usepackage{amssymb,amsmath}
\usepackage{ifxetex,ifluatex}
\usepackage{fixltx2e} % provides \textsubscript
\ifnum 0\ifxetex 1\fi\ifluatex 1\fi=0 % if pdftex
  \usepackage[T1]{fontenc}
  \usepackage[utf8]{inputenc}
\else % if luatex or xelatex
  \ifxetex
    \usepackage{mathspec}
    \usepackage{xltxtra,xunicode}
  \else
    \usepackage{fontspec}
  \fi
  \defaultfontfeatures{Mapping=tex-text,Scale=MatchLowercase}
  \newcommand{\euro}{€}
\fi
% use upquote if available, for straight quotes in verbatim environments
\IfFileExists{upquote.sty}{\usepackage{upquote}}{}
% use microtype if available
\IfFileExists{microtype.sty}{\usepackage{microtype}}{}
\ifxetex
  \usepackage[setpagesize=false, % page size defined by xetex
              unicode=false, % unicode breaks when used with xetex
              xetex]{hyperref}
\else
  \usepackage[unicode=true]{hyperref}
\fi
\hypersetup{breaklinks=true,
            bookmarks=true,
            pdfauthor={},
            pdftitle={Introduction},
            colorlinks=true,
            citecolor=blue,
            urlcolor=blue,
            linkcolor=magenta,
            pdfborder={0 0 0}}
\urlstyle{same}  % don't use monospace font for urls
\setlength{\parindent}{0pt}
\setlength{\parskip}{6pt plus 2pt minus 1pt}
\setlength{\emergencystretch}{3em}  % prevent overfull lines
\setcounter{secnumdepth}{0}

\usepackage{listings}
\usepackage{longtable}
\usepackage{booktabs}

\DeclareUnicodeCharacter{2227}{$\land$}
\DeclareUnicodeCharacter{22A2}{$\vdash$}
\DeclareUnicodeCharacter{2192}{$\rightarrow$}
\DeclareUnicodeCharacter{21D2}{$\Rightarrow$}
\DeclareUnicodeCharacter{27F9}{$\Longrightarrow$}
\DeclareUnicodeCharacter{03BB}{$\lambda$}
\DeclareUnicodeCharacter{27F8}{$\Longleftarrow$}


\begin{document}


"""



def usage():
	print "This is a Display Calculus project build script v0.1"
	print "Usage: ./build -c <calculus_file> -p <OUTPUT_PATH> -t <templates_path>"


def img_repl(matchobj):
	print matchobj.group(1)
	if "svg" not in matchobj.group(1):
		return "\\write18{wget -N " + matchobj.group(1).replace(r"\_", "_") + "}\n\\includegraphics[max width=\\textwidth]{" + matchobj.group(1).replace(r"\_", "_").split("/")[-1] + "}"
	else: return "\\input{" + matchobj.group(1).replace(r"\_", "_").split("/")[-1].split(".")[0] + "}"

def compile_latex(path):
	global TEX_CONST

	md = glob("*.md")
	# file = open(path + '/out.tex', 'w')
	# file.write( TEX_CONST )

	for p in md:

		name = re.sub("([0-9]{4}\-[0-9]{2}\-[0-9]{2})\-", "", p)
		name = name.replace(".md", "")

		p_str = open(p).read()
		p_str = re.sub(r"<div markdown=\"1\">\{\% highlight (\w+) \%\}", r"~~~", p_str)
		p_str = re.sub(r"\{\% highlight (\w+) \%\}", r"~~~", p_str)
		p_str = p_str.replace(r"{% endhighlight %}", "~~~")

		p_str = re.sub(r"!\[latex:(.+)\]\(.+\)", r"\\\1", p_str)


		p_str = re.sub(r"<br>.?!\[(.+)\]\((.+)\).?<br>", r"!\[\1]\(\2\)", p_str)

		p_str = re.sub(r"!\[.+\]\((.+)\)", r"~~~\nimg:\1\n~~~", p_str)

		p_str = re.sub(r"<img.+src=\"(.+)\".?>", r"~~~\nimg:\1\n~~~", p_str)

		p_str = p_str.replace("<span class=\"glyphicon glyphicon-exclamation-sign\"></span>", "\\danger")
		p_str = p_str.replace("<span class=\"glyphicon glyphicon-info-sign\"></span>", "\\info")

		p_file = open(name + '_tmp.md', 'w')
		p_file.write(p_str)
		p_file.close()

		cmd = "kramdown -o latex --html-to-native {0}".format(name + '_tmp.md')
		print cmd
		response,err = Popen(shlex.split(cmd), stdout=PIPE, stderr=PIPE).communicate()

		# if "error" in err.lower():
		# 	cmd = "kramdown -o latex {0}".format(name + '_tmp.md')
		# 	response,err = Popen(shlex.split(cmd), stdout=PIPE, stderr=PIPE).communicate()

		response = re.sub("(.+\n)+---\n", "", response)

		response = response.replace("\\textbackslash{}", "\\").replace(r"\\textless", r"\textless").replace("\\$", "$").decode("utf-8").replace(u" ", "").encode("utf-8").replace(r"LaTeX & {\tt p \vdash p}", r"LaTeX & {\tt p \textbackslash vdash p}").replace("\\newline", "").replace(r"alpha\_", "alpha_")

		response = re.sub("begin\{longtable\}\{\|(\w+)\|(\w+)\|\}", r"begin{tabularx}{\linewidth}{ \1 X }", response)
		response = re.sub("begin\{longtable\}\{\|(\w+)\|(\w+)\|(\w+)\|\}", r"begin{tabularx}{\linewidth}{ \1 \2 X }", response)
		response = re.sub("begin\{longtable\}\{\|(\w+)\|(\w+)\|(\w+)\|(\w+)\|\}", r"begin{tabularx}{\linewidth}{ \1 \2 \3 X }", response)

		response = response.replace(r"\end{longtable}", r"\end{tabularx}")

		# very hacky indeed -------------------------

		while True:
			if re.search(r"\\begin\{itemize\}\n\\item \\paragraph(((\n.+?)|(.+?\n))+?)\\end\{itemize\}", response) is None and re.search(r"\\begin\{itemize\}\n\\item \\subparagraph(((\n.+?)|(.+?\n))+?)\\end\{itemize\}", response) is None : break
			else: 
				response = re.sub(r"\\begin\{itemize\}\n\\item \\subparagraph(((\n.+?)|(.+?\n))+?)\\end\{itemize\}", r"\\subparagraph \1", response)
				response = re.sub(r"\\begin\{itemize\}\n\\item \\paragraph(((\n.+?)|(.+?\n))+?)\\end\{itemize\}", r"\\paragraph \1", response)

		response = re.sub(r"\\end\{itemize\}\n\\item ", r"\n", response)
		response = response.replace("\item \paragraph", "\paragraph")
		response = response.replace("\item \subparagraph", "\subparagraph")
		response = re.sub(r"\\end\{itemize\}\n\\end\{itemize\}", r"", response)

		# --------------------------------------------

		response = response.replace("verbatim", "spverbatim")

		response = response.replace("\\{", "{").replace("\\}", "}")

		# response = re.sub(r"\\\{\\\% highlight (\w+) \\\%\\\}", r"\\begin{minted}{\1}", response)
		# response = response.replace(r"\{\% endhighlight \%\}", r"\end{verbatim}")
		# response = response.replace("coq", "isabelle").replace(r"\textbar{}", r"|").replace(r"\guillemotright{}", ">>")

		response = re.sub(r"\\begin\{spverbatim\}img:(.+)\n\\end\{spverbatim\}", img_repl, response)

		response = re.sub(r"!\[.+\]\((.+)\)", img_repl, response)


		f = open('{0}/{1}.tex'.format(path, name), 'w')
		f.write( response )
		f.close()
		# if cmd_output_throws_error(flags, response, err, "Build failed!"): return False

		# file.write( "\include{" + name + "}\n" )

		os.remove(name + '_tmp.md')
	
	# file.write( "\n\end{document}" )
	# file.close()


def main(argv):
	try:
		opts, args = getopt.getopt(argv, "o:", ["output"])
	except getopt.GetoptError:
		usage()
		sys.exit(2)

	#user flag settings
	OUTPUT_PATH = "."

	for opt, arg in opts:
		if opt in ("-o", "--output"):
			OUTPUT_PATH = arg

	if OUTPUT_PATH.endswith("/"): OUTPUT_PATH = OUTPUT_PATH[:-1]
	#first compile the generator for core calculus
	compile_latex(OUTPUT_PATH)
	

if __name__ == "__main__":
	main(sys.argv[1:])