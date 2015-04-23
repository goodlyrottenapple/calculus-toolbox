---
layout: page
title: "Code generation"
category: doc
date: 2015-04-20 16:33:24
---

To make modifications to the [calculi]({{ site.baseurl }}/doc/calculi.html) (such as adding rules and/or connectives) easier, the calculus, originally formalized in Isabelle, was re-encoded in a JSON file and a set of Python scripts were created to generate the needed code for both Isabelle theories and Scala classes. The generator code itself was rewritten several times to facilitate easy extensibility and (hopefully) readability. These requirements were the main reason for using Python, which is great for quick and readable coding and scripting. The scripting abilities of Python allowed for easy file manipulation and generation.

### The build process

The full build process (invoked by `build.py`) goes through several stages of generating and compiling all the Isabelle theories and Scala classes. It is briefly outlined in the following diagram and expanded upon in detail in this section.

<br>

<img style="margin:0 auto;" class="img-responsive" alt="code generation diagram" src="https://rawgit.com/goodlyrottenapple/calculus-toolbox/gh-pages/_files/gen_dia.svg">

<br>

#### Load calculus description file

The JSON file passed to the build script is parsed and stored

<br>

#### Generate core calculus Isabelle theory

At this stage, the file [`template/Calc_Core.thy`](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/Calc_Core.thy) is filled in with the definitions of the calculus specified in the `calc_structure` portion of the JSON file.

##### Functions used

+   [calc_name_core]({{ site.baseurl }}/ref/isabellebuilder.html#calc_name_core)
+   [calc_structure]({{ site.baseurl }}/ref/isabellebuilder.html#calc_structure)
+   [export_path]({{ site.baseurl }}/ref/isabellebuilder.html#export_path)
+   [uncommentL]({{ site.baseurl }}/ref/isabellebuilder.html#uncomment)
+   [uncommentR]({{ site.baseurl }}/ref/isabellebuilder.html#uncomment)

<br>

#### Generate parser class for core calculus

Parsers for the data types defined in `calc_structure` are generated. The parsers are used to parse terms in the ASCII sugar notation, as this is the notation the user uses to input terms of the calculus into the UI. The ASCII notation is also used for saving the proof trees generated through the UI (unless the user specifically choses to export to Isabelle or LaTeX).

##### Functions used

+   calc_import
+   parser_calc_structure
+   parser_calc_structure_rules*
+   uncommentL
+   uncommentR

<br>

#### Generate print class for core calculus

The print class can generate the string representation of the calculus terms in Isabelle syntax, ASCII and as LaTeX. This allows the user to work with terms of the calculus within the toolbox UI and then typeset the resulting terms in LaTeX, export them back into Isabelle or save them in ASCII format for later manipulation within the UI.

##### Functions used

+   calc_import
+   print_calc_structure
+   print_calc_structure_rules*
+   uncommentL
+   uncommentR

<br>

#### Export Scala version of core calculus

The Isabelle theory file, generated in the previous step, is compiled in Isabelle and if it does not contain errors, will generate a Scala version/encoding of the calculus. The exported code includes the `datatype` definitions of the calculus terms.

{:.table}
   <span class="glyphicon glyphicon-exclamation-sign"></span> | `export_code`, the code export function in Isabelle, requires the explicit listing of all functions and definitions to be exported. This means that the top most type of the calculus (top most in the D.EAK and minimal calculus means the `Sequent` type, as it is the top most / biggest construction in the calculus) must be explicit given to the function. If `Sequent` is no longer the top/biggest term in the calculus, the `export_code` parameter must be manually amended in the [template file](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/Calc_Core.thy).

<br>

#### Compile Scala classes

This stage simply compiles all the Scala classes in the calculus source folder. `-J-Xmx1024m` flag is passed to the Scala compiler, because the auto generated calculus files (from Isabelle theory files) can get quite long and thus require more heap space. If compilation fails with these settings, the code generation might need to be optimized (or the generated code will have to be manually shortened). This should not be a problem, as some optimization has already been done and there is no problem in compiling the full D.EAK calculus at the moment.

<br>

#### Parse calculus rules and print for Isabelle

Since the rules of the calculus are encoded using the user defined ASCII sugar, they have to be parsed and then returned back in Isabelle format (the print class is used for this purpose). Whilst this may look complicated, and it is indeed the main reason why the calculus is generated in two stages and two separate Isabelle theory files, the reason for this decision was to make the encoding of the rules in the JSON file as easily readable as possible. As shown in the [calculi]({{ site.baseurl }}/doc/calculi.html) section, the Isabelle notation for DE (deep encoding) can become quite verbose and even unreadable. Another disadvantage of the Isabelle syntax with sugar is the need for the jEdit environment, if one wants to see the sugar notation. For example, in the Isabelle IDE, $p \vdash p$ shows up as:

<pre><code>(Atprop ''p'')<sub>FS</sub> ⊢ (Atprop ''p'')<sub>FS</sub></code></pre>

However, the underlying `.thy` file encodes the snippet in the following way:

~~~isabelle
(Atprop ''p'') \<^sub>F \<^sub>S \<turnstile> (Atprop ''p'') \<^sub>F \<^sub>S
~~~

The ASCII notation, if specified well, can thus greatly improve the readability and allow for sugar syntax without the need for the Isabelle IDE and Unicode symbols.

The parsing of the rules is done through the [Scala parser class](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/Parser.scala), which contains a main method that can be run from the terminal via `scala -classpath <path_to_bin> Parser <JSON_rule_list>`. Where `<JSON_rule_list>` is a list of Sequents in ASCII notation.

<br>

#### Generate calculus rules Isabelle theory

After the rules have been translated into Isabelle syntax, the rule encoding theory file for the calculus is generated from the [`Calc_Rules.thy`](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/Calc_Rules.thy) template.

##### Functions used

+   [calc_name]({{ site.baseurl }}/ref/isabellebuilder.html#calc_name)
+   [calc_structure_rules]({{ site.baseurl }}/ref/isabellebuilder.html#calc_structure_rules)
+   [export_path]({{ site.baseurl }}/ref/isabellebuilder.html#export_path)

<br>

#### Export Scala version of full calculus

Once the rule encoding theory file is successfully compiled by Isabelle, the Scala version of the full calculus (now including the encoded rules and proof trees)
is re-exported (even though there are two theory files in Isabelle, the resulting Scala code is exported into a single class).

<br>

#### Rebuild parser/print class for full calculus

The parser and print classes are rebuilt, now including the parsers and print functions for the full calculus.

<br>

#### Generate Scala UI classes

Builds the UI classes found in [`template/gui`](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/gui/)

##### Functions used

+   calc_import


<br>

*_This function is not called at this stage. For more information have a look at the reference page for this method_

