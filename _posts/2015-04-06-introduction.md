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

   ![F := ap ∈ AtProp | F ∧ F | F → F](https://raw.githubusercontent.com/goodlyrottenapple/calculus-toolbox/gh-pages/_files/intro1.png)
   
   And here is the corresponding definition in the JSON file:
   

