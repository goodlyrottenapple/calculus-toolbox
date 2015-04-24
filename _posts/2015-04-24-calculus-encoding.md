---
layout: page
title: "Calculus Encoding"
category: doc
date: 2015-04-20 16:13:26
---

The generator tools in the calculus toolbox use a single JSON file, which holds the full description of a display calculus, to generate all the Isabelle and Scala code. The JSON format was chosen because it is simple to use as has parsers in many languages, including Python and Scala. Using JSON files also allows storing data easily and passing data between different systems/languages. In Python, which is used for all the code generation, importing a JSON file is a one line command:

~~~python
imported_json = json.loads(json_file.read())
~~~

### Calculus file structure

A valid calculus description file is a JSON file with these four basic key-value pairs, the structure of which is documented below:

~~~json
{
    "calc_name" : ...,

    "calc_structure" : {
        ...
    },

    "calc_structure_rules" : {
        ...
    },

    "rules" : {
        ...
    }
}
~~~


#### calc_name

The value for `calc_name` is a string that holds the name of the calculus as it will appear in all Isabelle theories and Scala classes.

#### calc_structure

This section encodes the terms of the calculus, defined in Isabelle through the `datatype` definition.
The encoding of a type and its terms in Isabelle is transformed into the JSON file in the following way:

~~~isabelle
datatype <Term> = <Term_Constructor> <type> (<isabelle> [ [<p_1>, <p_2>,...<p_n>] <p_m> ]
~~~

The generic `datatype` definition above is 'disassembled' into the JSON file below.

~~~json
"<Term>" : {
    "<Term_Constructor>" : {
        "type" : "<type>",
        "isabelle" : "<isabelle>",
        "ascii" : "<ascii>",
        "latex" : "<latex>",
        "precedence": [ <p_1>, <p_2>,...<p_n>, <p_m> ]
    }
}
~~~

Note that none of the nested parameters (`type`, `isabelle`, `ascii`, etc.) are compulsory and can be omitted. Further details on the parameters used by the calculus toolbox generator tools are detailed here:

{: .table}
| Field      | JSON Data Type | Description |
| ---------- | -------------- | ------------ |
| type       | String         | Defines the values the constructor will hold (e.g. `string`, `int list`, ...) |
| isabelle   | String         | Defines the sugar syntax for the constructor |
| ascii      | String         | Defines the ASCII encoding, used to build the ASCII parser in Scala. If left undefined, will use the basic constructor syntax. |
| latex      | String         | Defines the LaTeX encoding, used to build the UI LaTeX typesetting and export functionality. If left undefined uses the basic constructor syntax. |
| precedence | Integer Array  | Defines the term biding for the syntactic sugar. __(Only implemented for Isabelle syntactic sugar at the moment)__ |

#### calc_structure_rules