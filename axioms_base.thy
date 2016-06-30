theory axioms_base
imports remove_notation
begin

text{* Before we begin, a note on Isabelle's HOL.
       According to \cite[BlPoTr14]:
       
       \begin{quote}
       By HOL we mean classical higher-order logic with Hilbert choice, 
       the axiom of infinity, and rank-1 polymorphism. HOL is based on
       Church's simple type theory [4]. It is the logic of Gordon's 
       system of the same name [5] and of its many successors. HOL is 
       roughly equivalent to ZF without support for classes and with the
       axiom of comprehension taking the place of the axiom of 
       replacement.\\

       [...] Beyond  HOL,  Paulson  and  Grabczewski  [14]  have 
       formalized  some  ordinal  and cardinal theory in Isabelle/ZF 
       following the usual set-theoretic recipe, via the class of
       ordinals with membership. Their main objective was to formalize
       several alternative statements of the axiom of choice, and hence 
       they invest care in avoiding this axiom for part of the cardinal
       theory. If our case, the Hilbert choice operator (effectively
       enforcing a bounded version of the axiom of choice) is pervasive.
       \end{quote}

       In fact we have the following lemma, to be found also in in
       "A Proof Assistant for Higher Order Logic" by Nikpow, Paulson,
       and Wenzel (page 87 of the 2015 version).
*}
(* WARNING: *)
lemma "(\<forall>x. \<exists>y. P x y) \<Longrightarrow> (\<exists>f. \<forall>z. P z (f(z)))"
using Hilbert_Choice.choice .  

text{* This means that we should be very careful when using metafunctions.  *}

section{* NBG Set Theory *}

text{* This is NBG Set theory as presented in "Chapter 4: Axiomatic
       Set Theory" by Mendelson, but based on Isabelle's Higher 
       Order Logic (HOL), instead of Mendelson's First Order Logic
       (FOL). According to Mendelson, this exposition follows 
       "G\"{o}del's monograph to a great extent, though there will be
       some key differences". Phrases in quotation marks or in a 
       quote environment (see e.g. below) will be phrases taken 
       from the relevant text in Mendelson's book, unless stated
       otherwise.

       \begin{quote} NBG has a single predicate letter $A^2_2$,
       but no function letters or individual constants [...] 
       is thought of as the membership relation.
       \end{quote}

       Since Isabelle is a typed system, we shall define first
       a primitive type ``Class'' for the objects of NBG Set Theory
       and denote the predicate letter $A^2_2$ by an Isabelle-
       -metafunction symbol, which is the canonical way to represent
       predicates in lambda calculus.
       *}

typedecl Class
axiomatization belongs :: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "\<in>" 78) 

abbreviation not_belongs (infixl "\<notin>" 78) 
where "X \<notin> Y \<equiv> \<not>(X \<in> Y)" -- "non-membership"

text{* In Mendelson, extensionality for classes is in fact the 
       definition of equality. Since we already have equality in 
       HOL, and since we want to use the same equality, we define
       extensionality as usual. *}

(*   page 226 *)
axiomatization 
  where extensionality: "(\<forall>Z::Class. (Z \<in> X \<longleftrightarrow> Z \<in> Y)) \<longleftrightarrow> (X = Y)"

definition
  subclass' :: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "\<subseteq>" 78 )
where "(X \<subseteq> Y) =  (\<forall>Z. (Z \<in> X \<longrightarrow> Z \<in> Y))"

definition 
  strict_subclass :: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "\<subset>" 78)
where "(X \<subset> Y) = (X \<subseteq> Y \<and> X \<noteq> Y)"

text{* The following lemmas are Proposition 4.1 in Mendelson. *} 

lemma Prop4_1_a: "(X=Y) \<longleftrightarrow> (X \<subseteq> Y \<and> Y \<subseteq> X)"
using extensionality subclass'_def by blast

text{* The following we get from HOL's definition of equality. *}

lemma Prop4_2_b: "X=X" ..

lemma Prop4_1_c: "(X=Y) \<longrightarrow> (Y=X)" by simp

lemma Prop4_1_d: "(X=Y) \<longrightarrow> ((Y=Z) \<longrightarrow> (X=Z))" by simp

lemma Prop4_1_e: "(X=Y) \<longrightarrow> (Z\<in>X \<longleftrightarrow> Z\<in>Y)"
by simp

text{* Sets are those classes that are members of another class. 
       The predicate Mendelson uses is called $M$, but we
       use $set$. We 
       shall reserve the symbol $\mathcal{V}$ for the universal 
       class. *}

text {* In Mendelson, the set predicate is M( ) but we shall use set( ). *}
definition set_predicate :: "Class \<Rightarrow> bool" ("set")
where "set(X) \<longleftrightarrow> (\<exists>Y::Class. X \<in> Y)"
notation set_predicate ("((_) is a set)" 70)

abbreviation not_a_set ("((_) is not a set)" 70)
where "(X is not a set) \<equiv> \<not>(X is a set)" 

definition proper_class_predicate:: "Class \<Rightarrow> bool" ("Pr")
where "Pr(X) \<longleftrightarrow> \<not>set(X)"

(* page 227 *)
text{* Exercise 4.1.: *}

lemma Ex4_1 [simp]: "Y \<in> X \<longrightarrow> set(Y)"
using set_predicate_def by blast

text{* At this point Mendelson introduces the equivalent of a 
       quantifier over the type of Sets. We shall define the 
       type Set as a subtype of Class. Before we can do that
       we need the set existence axiom and constants for the 
       universe and for the empty set, since no type can be 
       empty. We could also define a special quantifier over
       the type Set, but in the moment it doesn't seem 
       necessary. *}

axiomatization 
  universe :: Class ("\<V>") 
  where universe: "X \<in> \<V> \<longleftrightarrow> set(X)"
    and set_existence: "\<exists>X. set(X)"
    
typedef 
  Set = "Collect (\<lambda>A::Class. A \<in> \<V>)"
using set_existence universe by auto 

declare [[coercion_enabled]] -- "Enables the coersion below."
declare [[coercion Rep_Set]] -- "It adds the necessary Rep_Set automatically"
setup_lifting type_definition_Set 
    -- "something with Quotient_Set. Involves translations between Abs_Set and Rep_Set"
print_theorems


lemma obvious_set: "\<forall>x::Set. (x is a set)" using Rep_Set universe by auto


text{* Mendelson does not define the bounded quantifier "$\forall x \in Y$, but we do at this point
       to make the proofs more modern looking. *}


definition forall_in:: "Class \<Rightarrow> (Set \<Rightarrow> bool) \<Rightarrow> bool" 
  where "forall_in A \<phi> \<longleftrightarrow> (\<forall>x::Set. x \<in> A \<longrightarrow> \<phi>(x))" 

definition exists_in :: "Class \<Rightarrow> (Set \<Rightarrow> bool) \<Rightarrow> bool" 
  where "exists_in A \<phi> \<longleftrightarrow> (\<exists>x::Set. x\<in>A \<and> \<phi>(x))" 

                                  
text{* We denote these quantifiers as follows. *}

syntax (xsymbols)
  "_forall_in" :: "pttrn \<Rightarrow> Class \<Rightarrow> (Set \<Rightarrow> bool) => bool"
      ("(\<forall> _\<in>_./ _)" [0, 10] 10)
  "_exists_in" :: "pttrn \<Rightarrow> Class \<Rightarrow> (Set \<Rightarrow> bool) => bool"
      ("(\<exists> _\<in>_./ _)" [0, 10] 10)

translations 
  "\<forall> x \<in> A. \<phi>" == "CONST forall_in A (\<lambda>x. \<phi>)"
  "\<exists> x \<in> A. \<phi>" == "CONST exists_in A (\<lambda>x. \<phi>)"


(* From here on we have both type Class and type Set, and bounded quantification. *)


   

text{* Exercise 4.2 in Mendelson *}
lemma Ex4_2: 
  fixes X Y ::Class
  shows "(X=Y) \<longleftrightarrow> (\<forall>z::Set. (z \<in> X \<longleftrightarrow> z\<in>Y))"
by (metis Abs_Set_inverse extensionality mem_Collect_eq set_predicate_def universe)

lemmas set_extensionality = Ex4_2

text{* Mendelson's Axiom T is a theorem of HOL. *}
lemma axiom_T: 
  fixes X1 X2 X3 :: Class
  shows "(X1 = X2) \<longrightarrow> (X1 \<in> X3 \<longleftrightarrow> X2 \<in> X3)" by simp

lemma Ex4_3: "set(Z) \<and> (Z = Y) \<longrightarrow> set(Y)" by auto 

axiomatization 
  upair :: "Set \<Rightarrow> Set \<Rightarrow> Set" ("(1{_, _})")
where pairing: 
  "u \<in> {x,y}  \<longleftrightarrow> u = x \<or> u = y"

text{* We should introduce a new function symbol only after we
       prove that the unordered pair is unique, but then it 
       should be defined as:\\
       texttt{definition upair : Set $\Rightarrow$ Set $\Rightarrow$
       Set" ("(1$\{$\_, \_$\}$)")}\\
       \texttt{where "$\{$x,y$\}$ == (THE v. $\forall$u::Set. 
       (u$\in$v $\longleftrightarrow$ u = x $\lor$ u = y)"}\\
       Since we are uncertain about the ``THE''-operator, we 
       introduced first the upair function symbol above, and 
       we prove its uniqueness in the following lemma. The same 
       happens with the empty set later. *}


text{* \textbf{FOMUS workshop exercise:} *}

lemma Ex4_4: "\<forall>x y::Set. \<forall>u::Set. ((\<forall>z. (z\<in>u \<longleftrightarrow> z=x \<or> z=y)) \<longrightarrow> 
              (u = {x, y}))"

text{* 
\begin{quote} 
  This asserts that there is a unique set z, called the unordered pair of x and y, 
  such that z has x and y as its only members. Use axiom P and the extensionality principle. 
\end{quote}
*}
sorry


lemma Ex4_5: "\<forall>X :: Class. (X is a set) \<longleftrightarrow> (\<exists>y. X \<in> y)" 
using set_predicate_def by simp

lemma Ex4_6: "\<exists> M :: Class. (Pr(X) \<longrightarrow> (\<not> (\<forall> Y Z:: Class. \<exists> W ::Class. \<forall> U :: Class. 
                                           (U \<in> Z \<longleftrightarrow> (U = X) \<or> (U = Y)))))"
by (metis proper_class_predicate_def set_existence)

axiomatization empty :: Set ("\<emptyset>")
where empty_set: "\<forall>y. y \<notin> \<emptyset>"

(*   page 229 *) 

(*   comments after null set definition contain lemmas to be formalised. *)

abbreviation singleton :: "Set \<Rightarrow> Set"  ("(1{ _})")
where "{x} \<equiv> {x, x}"

text{* \textbf{FOMUS workshop exercise:} *}

lemma Ex4_7_a: "{X, Y} = {Y, X}"
sorry

lemma Ex4_7_b: "\<forall>x y. ({x} = {y}) \<longrightarrow> (x = y)"
by (metis Rep_Set_inject pairing)


end