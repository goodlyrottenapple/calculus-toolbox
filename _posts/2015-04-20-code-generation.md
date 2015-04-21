---
layout: page
title: "Code generation"
category: doc
date: 2015-04-20 16:33:24
---

To make modifications to the [calculi]({{ site.baseurl }}/doc/calculi.html) (such as adding rules and/or connectives) easier, the calculus, originally formalized in Isabelle, was re-encoded in a JSON file and a set of Python scripts were created to generate the needed code for both Isabelle theories and Scala classes. The generator code itself was rewritten several times to facilitate easy extensibility and (hopefully) readability. These requirements were the main reason for using Python, which is great for quick and readable coding and scripting. The scripting abilities of Python allowed for easy file manipulation and generation.

### The build process

The full build process (invoked by `build.py`) goes through several stages of generating and compiling all the Isabelle theories and Scala classes. It is briefly outlined in the following diagram and expanded upon in detail in this section.

<img style="margin:0 auto;" class="img-responsive" alt="code generation diagram" src="https://rawgit.com/goodlyrottenapple/calculus-toolbox/gh-pages/_files/gen_dia.svg">

#### Load calculus description file

The JSON file passed to the build script is parsed and stored

#### Generate core calculus Isabelle theory

At this stage, the file [`template/Calc_Core.thy`](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/Calc_Core.thy) is filled in with the definitions of the calculus specified in the `calc_structure` portion of the JSON file.

##### Functions used

+   calc_name_core
+   calc_structure
+   export_path
+   uncommentL
+   uncommentR


#### Generate parser class for core calculus

Parsers for the data types defined in `calc_structure` are generated. The parsers are used to parse terms in the ASCII sugar notation, as this is the notation the user uses to input terms of the calculus into the UI. The ASCII notation is also used for saving the proof trees generated through the UI (unless the user specifically choses to export to Isabelle or LaTeX).

##### Functions used

+   calc_import
+   parser_calc_structure
+   parser_calc_structure_rules*
+   uncommentL
+   uncommentR



#### Generate print class for core calculus

The print class can generate the string representation of the calculus terms in Isabelle syntax, ASCII and as LaTeX. This allows the user to work with terms of the calculus within the toolbox UI and then typeset the resulting terms in LaTeX, export them back into Isabelle or save them in ASCII format for later manipulation within the UI.

##### Functions used

+   calc_import
+   print_calc_structure
+   print_calc_structure_rules*
+   uncommentL
+   uncommentR

*_This function is not actually called at this stage. For more information have a look at the reference page for this method_

