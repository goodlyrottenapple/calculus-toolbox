---
layout: page
title: "Utilities"
category: doc
date: 2015-04-15 09:24:45
---

This section will outline the core functionality of this toolbox generator, namely the utilities used for generating the calculus tools.

### [build.py](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/build.py)
This is the main build script, which ties in all the utilities into a single script for easy calculus generation. The script takes the following set of parameters:

Flag:         |     |Arguments:                                                  |Description:
:-------------|-----|:-----------------------------------------------------------|:-------------------------------------------
`--path`      |`-p` |                                                            |Specify an output path for the calculus.
`--template`  |`-t` |                                                            |Specify a templates folder to be used.
`--verbose`   |`-v` |                                                            |Verbose mode.
`--build`     |`-b` |`all`, `scala`, `isabelle`                                  |Compile the specified files only. Defaults to `all`
`--stage`     |`-s` |`core_calc_gen`, `rule_calc_gen`, `calc_compile`, `add_gui` |Call a specific stage of the build.

#### Build Stages
The calculus toolbox is compiled from the calculus description file in several stages, which include compiling the core calculus Isabelle theory files, generating the ASCII parser and print classes in Scala, parsing and translating the encoded rules into Isabelle, generating the rule theory files and finally adding the UI Scala classes. Bellow is a short overview of these stages (you can manually call any stage of the build via the `--stage` flag) .

### `core_calc_gen`

##### Isabelle
The core calculus theory file is generated from [`template/Calc_Core.thy`](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/Calc_Core.thy). 

##### Scala
The parsers for the terms of the calculus are generated using [`template/Parser.scala`](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/Parser.scala)
<br>The print class for terms of the calculus is generated using [`template/Print.scala`](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/Print.scala)

### `calc_compile`

##### Scala
This stage simply compiles all the Scala classes in `<calculus_output_path>/src/scala`

### `rule_calc_gen`

##### Isabelle
The rules of the calculus encoded in the JSON file are parsed and encoded in the main Isabelle theory file ([`template/Calc_Rules.thy`](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/Calc_Rules.thy)). 

##### Scala
The parser class is rebuilt, now including parsers for proof trees and rule datatype constructors
<br>The print class is rebuilt, adding printing for proof trees and rule datatype constructors

### `add_gui`

##### Scala
Generates the Scala UI from [`template/gui/`](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/template/gui/) adding a separate compile script and a make file for the built calculus. 
<br>Any libraries inside the `libs` folder will be copied to the calculus folder.

### [gui.py](https://github.com/goodlyrottenapple/calculus-toolbox/blob/master/gui.py)
