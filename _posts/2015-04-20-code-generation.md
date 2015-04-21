---
layout: page
title: "Code generation"
category: doc
date: 2015-04-20 16:33:24
---

To make modifications to the [calculi]({{ site.baseurl }}/doc/calculi.html) (such as adding rules and/or connectives) easier, the calculus, originally formalized in Isabelle, was re-encoded in a JSON file and a set of Python scripts were created to generate the needed code for both Isabelle theories and Scala classes. The generator code itself was rewritten several times to facilitate easy extensibility and (hopefully) readability. These requirements were the main reason for using Python, which is great for quick and readable coding and scripting. The scripting abilities of Python allowed for easy file manipulation and generation.

### The build process

To build process goes through several stages of generating and compiling all the Isabelle theories and Scala classes. It is briefly outlined in the following diagram:

![code generation diagram](https://cdn.rawgit.com/goodlyrottenapple/calculus-toolbox/gh-pages/_files/gen_dia.svg)
