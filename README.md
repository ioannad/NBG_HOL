## NBG set theory in Isabelle's higher order logic (HOL), in a textbook fashion.

**We encourage you to work on this project with us!** In this case, please read the note to contributors below.

The initial files are heavily based on common work of: Marek Broll, Thekla Hamm, Uli Matzner, Lukas Meier, Robert Paßmann, Julian Schröteler, Jakob Speer, Thorben Tröbst, Benjamin Valdez, and Luisa Vogel, during the [winter semester 2015/16](http://www.math.uni-bonn.de/ag/logik/teaching/2015WS/praktikum_mathematische_logik.shtml). *Not all initial files have been uploaded.* They are:  remove_notation.thy, axioms_base.thy, ntuples.thy, auxiliary0.thy, FOL_formula.thy, FOL_substitution.thy, class_comprehension.thy, axioms_class_existence.thy, axioms_to_infinity.thy, auxiliary1.thy, ordinals.thy, equinumerosity.thy, finite_denumerable.thy, ordinal_arithmetic.thy, AC_AR.thy (might be uploaded with other name(s)).

This project is in cooperation with the [Mathematical Logic Group Bonn](www.math.uni-bonn.de/ag/logik).

### NBG set theory

Von Neumann-Bernays-Gödel (NBG) set theory is a finitely axiomatisable first order logic (FOL) set theory, which can talk about classes and sets (the elements of the classes). It is a conservative extension of Zermelo-Fraenkel (ZF) set theory, which means that they prove the same theorems about sets. The comprehension axiom schema of ZF is a single axiom of NBG, which is made possible by the 7 "Class Existence Axioms" that give rise to FOL definable classes. To ensure we only have FOL- and not HOL- definable classes, the theories FOL_formula, FOL_substitution, and class_comprehension are developed.

### Isabelle/HOL

Isabelle/HOL is the main logic branch of the proof assistant [Isabelle](https://isabelle.in.tum.de). It is classical HOL with rank-1 polymorphism, with the axioms of infinity and Hilbert choice, and with a mechanism for overloading constant and type definitions. It includes a set theory, which is comparable to ZFC plus an inaccessible cardinal. *We are very carefully trying not to introduce choice functions from the background logic into our theory*. 

**Sledgehammer** is a powerful tool for Isabelle/HOL, which gathers relevant lemmas, drops type requirements, and feeds the contexts and the goals to established fully automated FOL provers, such as the E prover, SPASS, Z3, cvc4, and Vampire. It returns suggestions, which almost always work. In this way, novice contributors can quickly bridge larger gaps in their formal proofs (often just as in a textbook), without having to know all the theory files and relevant lemmas. 

**Isar** (intelligible semi automated reasoner) is a proving language for Isabelle, which resembles human proofs with the use of words such as "proof", "assume", "then have", "obtain", "qed". See an example below.

**Textbook likeness** is important to attract set theorists as contributors, especially for the later files, and because it aids proof understanding and creation.

### The theory files

In these theories, the formalisation is presented in an almost linear manner (textbook). The dependencies are listed below, with the first theory in the list requiring only Main (of HOL).

Main branch
-----------
* `remove_notation`  -- Removes internal notation so it can be redefined.
* `axioms_base` -- The base of the theory: in-relation, class extensionality, universal class, set existence, pairing, and empty set.
* `auxiliary0`-- Some extra lemmas
* `ntuples` -- Definitions and lemmas about n-tuples
* `axioms_class_existence` -- The "Class Existence Axioms" B1-B7
* `FOL_formula`, `FOL_substitution`, `class comprehension` enable the {x|phi} notation for classes, for first order formulas phi, by proving the Class Existence Theorem.
* `axioms_to_infinity` contains the axioms: union (sum set), powerset, subsets (together with the Class Existence Theorem makes the axiom schema of comprehension), replacement, and infinity. 

Development branch
------------------
* `ordinals` starts with some relation properties, functions, and classes related to ordinal numbers. Transfinite induction is proved here in three forms.
The last lemmas involve bijective maps leading to the next theory `equinumerosity`  (TBU - to be uploaded)

### Note to contributors

We would be happy if you want to contribute! Please add any changes, theories, or tactics in an own branch (clone "development"), or fork the whole repository. 

**How can you contribute?** You can either help by filling in those skipped "sorry" proofs in the files of the "development" branch, or create your own theories formalising your own research field, or look for standard proofs and write ML or Eisbach tactics for these proofs, or proofread and improve the existing theory files.

Preliminary standard operating proceedure:
* Only contribute proofs written in Isar. 
* When defining priorities, use numbers around 60-90 as follows:
 ** functions from two or more sets/classes to a set/classe get 79 or 80, e.g., intersection of two sets is 80 but cartesian product is 79, so (A intersection B times C) = ((A intersection B) times C) 
 ** relations, such as the in-relation get 78
 ** predicates (metafunctions to bool) and text-like notation ("_ is a set") get 70, their arguments 71, if necessary.
* **Do not use the tactic smt**, even if Sledgehammer suggests so, as it is considered unsafe. 
* Write as you would write a textbook.
* Write texts and explanations to your definitions and theorems, using `text{* ... *}` and `section{* ... *}`, where `...` should be LaTeX formatted text.
* Indent in a readable manner where necessary. Try to roughly follow the writting style of the existing theory files.
* In case of any uncertainty or problems with the files, please do raise GitHub issues, so that we can find a solution.
* Regularly ask Sledgehammer to try and prove `False` (With `lemma False sledgehammer`). If Sledgehammer manages, or gives any indication towards a proof of False, do raise an issue!!

* **`sorry`-proofs in the main branch:** Please do not add proofs to these lemmas, they shall be excercises during the workshop at [FOMUS in Bielefeld](http://fomus.weebly.com).

*A word of warning - formal proving can be addictive! :)*

-----------------------------------------------------------------------
