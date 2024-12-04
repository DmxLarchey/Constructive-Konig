```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# Constructive substitutes for König's lemma (artifact)

This project is composed of a Coq artifact for the TYPES 2024 post-proceedings submission
[_Constructive substitutes for König's lemma_](https://members.loria.fr/DLarchey/files/papers/types-post-2024.pdf) by Dominique Larchey-Wendling.

The standalone Coq file [`constructive_konig.v`](constructive_konig.v)
contains the developement and is largely commented. It has minimal dependencies, only on the standard 
library (distributed with Coq), and only on the `List`, `Arith`, `Lia`, `Permutation` and `Utf8` modules within the standard library. 
It is intented to be read and executed within an IDE for Coq such as eg [CoqIDE](https://coq.inria.fr/download) or 
[vscoq](https://github.com/coq-community/vscoq). 

Any version of Coq starting from `8.14` and upto at least `8.20` should be ok 
to compile and/or review the file [`constructive_konig.v`](constructive_konig.v).
Since this is a single file, there is no need to pre-compile before reviewing. 

# Remarks

Concerning the use of `Utf8` symbols in the code, we did not experience any display issues 
with CoqIDE in any of the [`opam` installed](https://coq.inria.fr/opam-using.html) versions from `8.14` and `8.20`. 
Similarly, viewing the code in the Chrome browser directly on GitHub looks fine on our systems. 
Depending on the operating system, distribution or the IDE/browser, such issues might 
possibly arise if OS installed `Utf8` symbols are incomplete/inconsistent with the IDE/browser. 

Anyway, to possibly avoid such issues, we suggest the usage of an `opam` installed version 
of CoqIDE rather than the default OS version of the tool. This also allows to easily switch
between different versions of Coq when developping general purpose code.
