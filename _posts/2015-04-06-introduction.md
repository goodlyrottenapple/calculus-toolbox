---
layout: page
title: "Introduction"
category: doc
date: 2015-04-06 20:09:04
---

The calculus toolbox is a set of scripts and utilities for generating a custom set of Isabelle theory files and Scala classes that provide a user interface for working with set calculi.

### System overview

The specification of a calculus file is contained within a JSON file. This file contains the full specification of the structure of the calculus, as well as the encoding of the rules of the calculus. The specifics on the JSON file structure can be found HERE.

The `utilities` folder contains the core scripts for generating the Isabelle theory files and the Scala UI. Detailed description of these tools can be found HERE.

Finally, the generated Scala and Isabelle files are documented in HERE.

### Getting started

To get started quickly, this tutorial will guide you through the process of generating a custom calculus.

1. First open the default calculus template `default.json` and edit the calculus name:

   ~~~json
   "calc_name" : "EAKMin"
   ~~~

   This name is used in all the Isabelle theory files and Scala classes.
   
2. Next, let's have a look at the definition of the calculus structure, more specifically at the definition of atomic propositions and formulas. The inductive definition for these is given below:

   \\( F:= ap \in AtProp \mid F \land F \mid F \rightarrow F \\)

   And here is the corresponding definition in the JSON file:

   ~~~json
   "Atprop" : {
      "Atprop" : {
         "type" : "string",
         "ascii" : "_"
      },
      "Atprop_Freevar" : {
         "type" : "string",
         "isabelle" : "?\\<^sub>A _",
         "ascii" : "A? _",
         "latex" : "_",
         "precedence": [320, 320]
      }
   },

   "Formula" : {
      "Formula_Atprop" : {
         "type": "Atprop",
         "isabelle" : "_ \\<^sub>F",
         "precedence": [320, 330]
      },
      "Formula_Freevar" : {
         "type" : "string",
         "isabelle" : "?\\<^sub>F _",
         "ascii" : "F? _",
         "latex" : "_",
         "precedence": [340, 330]
      },
      "Formula_Bin" : {
         "type" : ["Formula", "Formula_Bin_Op", "Formula"],
         "isabelle" : "B\\<^sub>F _",
         "precedence": [330,330,330, 331]
      }
   },

   "Formula_Bin_Op" : {
      "Formula_And" : {
         "isabelle" : "\\<and>\\<^sub>F",
         "ascii" : "^",
         "latex" : "\\wedge"
      },
      "Formula_ImpR" : {
         "isabelle" : "\\<rightarrow>\\<^sub>F",
         "ascii" : ">",
         "latex" : "\\rightarrow"
      }
   }
   ~~~

   Note that this is a deep embedding (abbreviated DE) of the calculus in Isabelle, which means that...

   ...for every type in the calculus a _Freevar term is added to the DE
      
   ...for every n-ary connective, a _Zer/Un/Bin/.. term is added to the DE of the corresponding type and a separate type of the following form is added:


   ~~~json
   "<Type>_<Zer/Un/Bin>_Op" : {
         "<Type>_<Connective>" : {
            ...
         }
      }
   ~~~

   ...a type can be promoted into another type through a constructor of the following shape:

   ~~~json
   "<Type>_<Type>" : {
      "type": "<Type1>",
      ...
   }
   ~~~

   The terms are built inductively in this definition by specifying the ``type`` parameter in the JSON file. For example, a binary connective for a formula is specified via the entry ``"type" : ["Formula", "Formula_Bin_Op", "Formula"]`` in the ``Formula`` declaration, with the corresponding declaration of the binary connective(s) in ``Formula_Bin_Op``

   To get a better idea of what the other specified parameters in the definition of ``Atprop``, ``Formula`` and ``Formula_Bin_Op`` mean, let's have a look at the the Isabelle definitions, generated from the JSON snippet above.

   ~~~coq
   datatype Formula_Bin_Op = Formula_And ("\<and>\<^sub>F")
                           | Formula_ImpR ("\<rightarrow>\<^sub>F")

   datatype Atprop = Atprop string
                   | Atprop_Freevar string ("?\<^sub>A _" [320] 320)

   datatype Formula = Formula_Atprop Atprop ("_ \<^sub>F" [320] 330)
                    | Formula_Bin Formula Formula_Bin_Op Formula ("B\<^sub>F _ _ _" [330,330,330] 331)
                    | Formula_Freevar string ("?\<^sub>F _" [340] 330)
   ~~~

   The parameter ``isabelle`` together with ``precedence`` (in the JSON file) specify the sugar syntax of the defined terms in Isabelle. Either/both of the parameters can be ommited as in the case of the constructor/term ``Atprop`` in the datatype/type ``Atprop``.

   We similarly define structural terms:

   \\( S:= F \mid Id \mid S \,; S \mid S > S \\)

   and sequents:

   \\( S \vdash S \\)

   To see the corresponding JSON entries for these types, check ``default.json``
      
3. The next part of the JSON file contains the encoded rules of the calculus. The encoding of the rules is tied to the definition of the calculus, more specifically to the ASCII sugar defined in the previous step.
   
   To demonstrate, here is a look at the different encodings of a simple sequent \\( p \vdash p \\):

   Notation/Sugar:           | Code:
   --------------------------|---------------------------------------------------------------------------------------------------------------------
   No sugar:                 | ``Sequent (Structure_Formula (Formula_Atprop (Atprop ''p''))) (Structure_Formula (Formula_Atprop (Atprop ''p'')))``
   Isabelle:                 | ``((Atprop ''p'') \<^sub>F) \<^sub>S \<turnstile> ((Atprop ''p'') \<^sub>F) \<^sub>S``
   ASCII:                    | ```p |- p```
   LATEX:                    | ``p \vdash p``

   aa