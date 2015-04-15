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

   ```js
"calc_name" : "EAKMin"
   ```
   
   This name is used in all the Isabelle theory files and Scala classes.
   
2. Next, let's have a look at the definition of the calculus structure, more specifically at the definition of atomic propositions and formulas. The inductive definition for these is given below:

   ![F \:\= ap ∈ AtProp \| F ∧ F \| F → F](https://raw.githubusercontent.com/goodlyrottenapple/calculus-toolbox/gh-pages/_files/intro1.png)


   
   And here is the corresponding definition in the JSON file:
   
   ```js
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
   ```

   Note that this is a deep embedding (abbreviated DE) of the calculus in Isabelle, which means that:
   
   - for every type in the calculus a ``_Freevar`` term is added to the DE
   - for every n-ary connective, a ``_Zer/Un/Bin/..`` term is added to the DE of the corresponding type and a separate type of the following form is added:

      ```json
      "<Type>_<Zer/Un/Bin>_Op" : {
         "<Type>_<Connective>" : {
            ...
         }
      }
      ```
   - a type can be promoted into another type as through a constructor of the following shape

   ```json
      "<Type>_<Type>" : {
         "type": "<Type1>",
         ...
      }
   ```
   
   The terms are built inductively in this definition by specifying the ``type`` parameter in the JSON file. For example, a binary connective for a formula is specified via the entry ``"type" : ["Formula", "Formula_Bin_Op", "Formula"]`` in the ``Formula`` declaration, with the corresponding declaration of the binary connective(s) in ``Formula_Bin_Op``
   
   To get a better idea of what the other specified parameters in the definition of ``Atprop``, ``Formula`` and ``Formula_Bin_Op`` mean, let's have a look at the the Isabelle definitions, generated from the JSON snippet above.
   
   ```lua
   datatype Formula_Bin_Op = Formula_And ("\<and>\<^sub>F")
                           | Formula_ImpR ("\<rightarrow>\<^sub>F")

   datatype Atprop = Atprop string
                   | Atprop_Freevar string ("?\<^sub>A _" [320] 320)

   datatype Formula = Formula_Atprop Atprop ("_ \<^sub>F" [320] 330)
                    | Formula_Bin Formula Formula_Bin_Op Formula ("B\<^sub>F _ _ _" [330,330,330] 331)
                    | Formula_Freevar string ("?\<^sub>F _" [340] 330)
   ```
   
   It is easy to see that the parameter ``isabelle`` together with ``precedence`` (in the JSON file) specify the sugar syntax of the defined terms in Isabelle. Either/both of the parameters can be ommited as in the case of the constructor ``Atprop`` in the datatype ``Atprop``.
   
   aaaaaaba
