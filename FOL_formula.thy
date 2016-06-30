theory FOL_formula
imports axioms_class_existence auxiliary0
begin

text{* A first order logic (FOL) term is either a variable indexed by Isabelle's built in 
       natural numbers (\texttt{FVar nat}) or a constant of type \texttt{Class}. 
*}
datatype FOL_Term = FVar nat | FConst Class

text{* An FOL formula for NBG is either built from FOL Terms as follows. The names 
       given are the standard names for building formulas, with an \texttt{F} in the front
       to differentiate these formulas from Isabelle's built-in HOL counterparts. *}
datatype FOL_Formula =
  FTrue | FFalse | FBelongs FOL_Term FOL_Term | FEquals FOL_Term FOL_Term
  | FAnd FOL_Formula FOL_Formula | FOr FOL_Formula FOL_Formula | FNot FOL_Formula
  | FImp FOL_Formula FOL_Formula | FIff FOL_Formula FOL_Formula
  | FEx nat FOL_Formula | FAll nat FOL_Formula

text{* A FOL evaluation takes a \texttt{FOL_Term} and an interpretation of the variables to sets 
       (a metafunction from \texttt{nat} to \texttt{Set}), and returns a set or a class, 
       depending on which of the two FOL terms it evaluates.  *}
primrec FOL_Eval :: "FOL_Term \<Rightarrow> (nat \<Rightarrow> Set) \<Rightarrow> Class"
where
  "FOL_Eval (FVar n) i = i(n)"
  | "FOL_Eval (FConst c) i = c"

text{* The function \texttt{Update} takes an interpretation \texttt{i} of variables to sets, an
       Isabelle-natural number \texttt{n} (of type \texttt{nat}), and a set \texttt{x}, and 
       returns an interpretation that sends the \texttt{n}-th set-variable to \texttt{x}. *}
definition Update :: "[nat \<Rightarrow> Set, nat, Set] \<Rightarrow> (nat \<Rightarrow> Set)"
where "Update f n x = (\<lambda>k. if k = n then x else f(k))"

text{* The function \texttt{FOL_True} evaluates a FOL formula, given an interpretation, 
       to Isabelle's \texttt{True}/\texttt{False}. *}
primrec FOL_True :: "FOL_Formula \<Rightarrow> (nat \<Rightarrow> Set) \<Rightarrow> bool"
where
  "FOL_True FTrue i = True"
  | "FOL_True FFalse i = False"
  | "FOL_True (FBelongs x y) i = FOL_Eval x i \<in> FOL_Eval y i"
  | "FOL_True (FEquals x y) i = (FOL_Eval x i = FOL_Eval y i)"
  | "FOL_True (FAnd \<phi> \<psi>) i = ((FOL_True \<phi> i) \<and> (FOL_True \<psi> i))"
  | "FOL_True (FOr \<phi> \<psi>) i = ((FOL_True \<phi> i) \<or> (FOL_True \<psi> i))"
  | "FOL_True (FNot \<phi>) i = (\<not>(FOL_True \<phi> i))"
  | "FOL_True (FImp \<phi> \<psi>) i = ((FOL_True \<phi> i) \<longrightarrow> (FOL_True \<psi> i))"
  | "FOL_True (FIff \<phi> \<psi>) i = ((FOL_True \<phi> i) \<longleftrightarrow> (FOL_True \<psi> i))"
  | "FOL_True (FEx n \<phi>) i = (\<exists>y :: Set. FOL_True \<phi> (Update i n y))"
  | "FOL_True (FAll n \<phi>) i = (\<forall>y :: Set. FOL_True \<phi> (Update i n y))"
  

text{* \texttt{FOL_Var} returns the number of a FOL Term, if that Term is a FOL set-variable
       (\texttt{FVar}), otherwise it returns 0. For this reason, we should never use 0 for an 
       \texttt{FVar}, when we are defining our own FOL formulas. *}
primrec FOL_Var :: "FOL_Term \<Rightarrow> nat"
where
  "FOL_Var (FVar n) = n"
  | "FOL_Var (FConst c) = 0"

text{* \texttt{FOL_MaxVar} takes a FOL formula and returns the largest variable number 
       of all the variables occurring in the formula (includes bound variables). Useful 
       when we want to be sure that we are using a variable that doesn't occur in a formula. *}
primrec FOL_MaxVar :: "FOL_Formula \<Rightarrow> nat"
where
  "FOL_MaxVar FTrue = 0"
  | "FOL_MaxVar FFalse = 0"
  | "FOL_MaxVar (FBelongs x y) = max (FOL_Var x) (FOL_Var y)"
  | "FOL_MaxVar (FEquals x y) = max (FOL_Var x) (FOL_Var y)"
  | "FOL_MaxVar (FAnd \<phi> \<psi>) = max (FOL_MaxVar \<phi>) (FOL_MaxVar \<psi>)"
  | "FOL_MaxVar (FNot \<phi>) = FOL_MaxVar \<phi>"
  | "FOL_MaxVar (FOr \<phi> \<psi>) = max (FOL_MaxVar \<phi>) (FOL_MaxVar \<psi>)"
  | "FOL_MaxVar (FImp \<phi> \<psi>) = max (FOL_MaxVar \<phi>) (FOL_MaxVar \<psi>)"
  | "FOL_MaxVar (FIff \<phi> \<psi>) = max (FOL_MaxVar \<phi>) (FOL_MaxVar \<psi>)"
  | "FOL_MaxVar (FEx n \<phi>) = FOL_MaxVar \<phi>"
  | "FOL_MaxVar (FAll n \<phi>) = FOL_MaxVar \<phi>"

lemma FOL_MaxVar_Dom: 
  shows "\<forall> i j :: (nat \<Rightarrow> Set). (\<forall>(k::nat) \<le> FOL_MaxVar \<phi>. i(k) = j(k)) \<longrightarrow> 
                                (FOL_True \<phi> i \<longleftrightarrow> FOL_True \<phi> j)"
text{* For all $i$, $j$ interpretations, if the interpretations 
       $i$ and $j$ agree on every every Isabelle-natural number $k$ that is less than the largest 
       variable index occurring in a FOL_Formula $\phi$, then $i$ and $j$ result in the same 
       \texttt{FOL_True}-evaluation of $\phi$. *} 
proof (induction \<phi>, simp_all; rule allI, rule allI, rule impI)
                                                          --"By induction on FOL_Formula complexity" 
  fix x1 x2 :: "FOL_Term"
  fix i j   :: "nat \<Rightarrow> Set"
  assume assm1: "(\<forall>k\<le>max (FOL_Var x1) (FOL_Var x2). i k = j k)"
  thus 1: "(FOL_Eval x1 i \<in> FOL_Eval x2 i \<longleftrightarrow> FOL_Eval x1 j \<in> FOL_Eval x2 j)" 
    by (metis FOL_Eval.simps(1) FOL_Eval.simps(2) FOL_Term.exhaust FOL_Var.simps(1) max.cobounded1 
      max.cobounded2)      
  from assm1 show 2: "(FOL_Eval x1 i = FOL_Eval x2 i) \<longleftrightarrow> (FOL_Eval x1 j = FOL_Eval x2 j)"
    by (metis FOL_Eval.simps(1) FOL_Eval.simps(2) FOL_Term.exhaust FOL_Var.simps(1) max.cobounded1 
      max.cobounded2)  
(* Identical proof as above, show 1 and 2 doesn't work. Would be nice to have a "similarly" 
   (or, more precicely, a "exactly as above"). *)
next
  fix \<phi>1 \<phi>2 :: FOL_Formula 
  fix i j    :: "nat \<Rightarrow> Set"
  assume IH\<phi>1:  "\<forall>i j. (\<forall>k\<le>FOL_MaxVar \<phi>1. i(k) = j(k)) \<longrightarrow> FOL_True \<phi>1 i = FOL_True \<phi>1 j"
     and IH\<phi>2:  "\<forall>i j. (\<forall>k\<le>FOL_MaxVar \<phi>2. i(k) = j(k)) \<longrightarrow> FOL_True \<phi>2 i = FOL_True \<phi>2 j"
     and assm2: "\<forall>k\<le>max (FOL_MaxVar \<phi>1) (FOL_MaxVar \<phi>2). i(k) = j(k)"
  show 3: " (FOL_True \<phi>1 i \<and> FOL_True \<phi>2 i) \<longleftrightarrow> (FOL_True \<phi>1 j \<and> FOL_True \<phi>2 j)"
    by (metis IH\<phi>1 IH\<phi>2 assm2 dual_order.trans max.cobounded2 max_def)
  show 4: "(FOL_True \<phi>1 i \<or> FOL_True \<phi>2 i) \<longleftrightarrow> (FOL_True \<phi>1 j \<or> FOL_True \<phi>2 j)"
    by (metis IH\<phi>1 IH\<phi>2 assm2 dual_order.trans max.cobounded2 max_def)
  show 5: "(FOL_True \<phi>1 i \<longrightarrow> FOL_True \<phi>2 i) \<longleftrightarrow> (FOL_True \<phi>1 j \<longrightarrow> FOL_True \<phi>2 j)"
    by (metis IH\<phi>1 IH\<phi>2 assm2 dual_order.trans max.cobounded2 max_def)
  show 6: "(FOL_True \<phi>1 i = FOL_True \<phi>2 i) = (FOL_True \<phi>1 j = FOL_True \<phi>2 j)"
    by (metis IH\<phi>1 IH\<phi>2 assm2 dual_order.trans max.cobounded2 max_def)
next 
  fix n :: nat 
  fix \<phi> :: FOL_Formula
  fix i j :: "nat \<Rightarrow> Set" 
  assume IH\<phi>:   "\<forall>i j. (\<forall>k\<le>FOL_MaxVar \<phi>. i k = j k) \<longrightarrow> FOL_True \<phi> i = FOL_True \<phi> j"
     and assm3: "\<forall>k\<le>FOL_MaxVar \<phi>. i k = j k" 
  show 8: "(\<forall>y::Set. FOL_True \<phi> (Update i n y)) \<longleftrightarrow> (\<forall>y::Set. FOL_True \<phi> (Update j n y))"
    unfolding Update_def using IH\<phi> assm3 by (metis (no_types, lifting)) 
  thus 7: "(\<exists>y::Set. FOL_True \<phi> (Update i n y)) \<longleftrightarrow> (\<exists>y::Set. FOL_True \<phi> (Update j n y))"
    unfolding Update_def using IH\<phi> assm3 by (metis (no_types, lifting))
qed

text{* The following predicate is what we are aiming for. For class comprehension we
       want to show that for every FOL\_Formula and every Isabelle-natural number $n$, 
       there exists a class $C$ that contains exactly those tuples, which satisfy $\phi$. *}

definition Class_Ex :: "FOL_Formula \<Rightarrow> nat \<Rightarrow> bool"
where "Class_Ex \<phi> n \<equiv> \<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> FOL_True \<phi> i"
-- "There exists a class C which contains exactly those (n+1)-tuples which satisfy \<phi>. 
    We want to show that this is always true, for any FOL_Formula \<phi> and for n largest index 
    appearing in \<phi> (lemma Class_Existence)."

lemma Class_Ex_Mono: "Class_Ex \<phi> (FOL_MaxVar \<phi>) \<Longrightarrow> Class_Ex \<phi> (FOL_MaxVar \<phi> + k)"
text{* If there is a class that contains all the \tt{n+1}-tuples which satisfy \tt{$\phi$}, where 
       \tt{n} is the largest variable index occurring in \tt{$\phi$}, then for any \tt{k::nat}, 
       there is a class that contains all the \tt{(n+k+1)}-tuples with this property. *}
proof -
  assume "Class_Ex \<phi> (FOL_MaxVar \<phi>)"
  then obtain C where C_def: "\<forall>i. \<langle>\<dots>, i(FOL_MaxVar \<phi>)\<rangle> \<in> C \<longleftrightarrow> FOL_True \<phi> i"
    unfolding Class_Ex_def by blast
  then obtain D where "\<forall>i. \<langle>\<dots>, i(FOL_MaxVar \<phi> + k)\<rangle> \<in> D \<longleftrightarrow> \<langle>\<dots>, i(FOL_MaxVar \<phi>)\<rangle> \<in> C"
    using Ex_4_11_d by blast
  with C_def have "\<forall>i. \<langle>\<dots>, i(FOL_MaxVar \<phi> + k)\<rangle> \<in> D \<longleftrightarrow> FOL_True \<phi> i" by blast
  thus ?thesis unfolding Class_Ex_def by blast
qed

lemma Class_Ex_Mono2: "\<lbrakk>FOL_MaxVar \<phi> \<le> n; Class_Ex \<phi> (FOL_MaxVar \<phi>)\<rbrakk> \<Longrightarrow> Class_Ex \<phi> n"
text{* Consequently, if $n$ is greater or equal to $m$, the largest variable index occurring
       in $\phi$, and if there is a class containing all the $m$-tuples that satisfy $\phi$ under
       any interpretation, then there is a class containing all the $n$-tuples that satisfy
       $\phi$ under any interpretation. *} 
using Class_Ex_Mono le_Suc_ex by blast

text{* To prove that for any FOL formula $\phi$, there is a class that contains all the 
       sets that appear last in an $n$-tuple which satisfies $\phi$ under any interpretation, 
       we prove the following lemmas, towards an induction on the complexity of FOL formulas. *}

lemma Class_Ex_True: "Class_Ex FTrue n" --"Atomic case FOL's True."
unfolding Class_Ex_def using Ex4_9_b by (simp, blast)

lemma Class_Ex_False: "Class_Ex FFalse n" --"Atomic case FOL's False."
unfolding Class_Ex_def using empty_set by (simp, blast)

lemma Class_Ex_Belongs_CC: "Class_Ex (FBelongs (FConst c) (FConst d))
  (FOL_MaxVar (FBelongs (FConst c) (FConst d)))" --"Atomic case \<in>-relation with Class-constants"
proof (unfold Class_Ex_def, simp)
  show "\<exists>C. \<forall>i :: nat \<Rightarrow> Set. i 0 \<in> C = c \<in> d"
  proof (cases "c \<in> d")
    assume "c \<in> d"
    thus ?thesis using Ex4_9_b by auto
  next
    assume "c \<notin> d"
    thus ?thesis using empty_set by auto
  qed
qed

lemma Tuple_Last: "\<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> i(n) \<in> X"
proof (cases "n = 0")
  assume "n = 0"
  thus ?thesis by auto
next
  assume "n \<noteq> 0"
  then obtain l where "n = Suc l" using not0_implies_Suc by blast
  moreover obtain C where "\<forall>v. \<forall>i. \<langle>\<dots>, i(l), v\<rangle> \<in> C \<longleftrightarrow> v \<in> X" using Ex_4_11_f by blast
  ultimately have "\<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> i(n) \<in> X" by simp
  thus ?thesis ..
qed

lemma Class_Ex_Belongs_VC: "Class_Ex (FBelongs (FVar n) (FConst c)) 
  (FOL_MaxVar (FBelongs (FVar n) (FConst c)))"
--"Atomic case \<in>-relation with a Set-variable and a Class-constant"
by (unfold Class_Ex_def, simp, blast intro: Tuple_Last)

lemma Tuple_Extend1: "\<exists>C. \<forall>i. \<langle>\<dots>, i(Suc k), i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(k), i(n)\<rangle> \<in> X"
using Ex_4_11_b by (simp, blast)

lemma Tuple_Extend2: "n > 0 \<Longrightarrow> \<forall>X. \<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n - Suc m), i(n)\<rangle> \<in> X"
proof (induct "m", simp_all)
  assume "0 < n"
  then have "Suc (n - Suc 0) = n" by simp
  hence "\<forall>i. \<langle>\<dots>, i(n)\<rangle> = \<langle>\<dots>, i(n - Suc 0), i(n)\<rangle>" by (metis ToTuple.simps(2))
  thus "\<forall>X. \<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n - Suc 0), i(n)\<rangle> \<in> X" by auto
next
  fix m
  assume a1: "\<forall>X. \<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n - Suc m), i n\<rangle> \<in> X"
  assume "0 < n"
  show "\<forall>X. \<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n - Suc (Suc m)), i n\<rangle> \<in> X" 
  proof (rule allI, cases "Suc m \<ge> n")
    fix X
    assume "n \<le> Suc m"
    hence "n - Suc (Suc m) = n - Suc m" by simp
    with a1 show "\<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>,  i(n - Suc (Suc m)), i n\<rangle> \<in> X" by simp
  next
    fix X
    assume "\<not> n \<le> Suc m"
    hence eq: "n - Suc m = Suc (n - Suc (Suc m))" by simp
    obtain C where C_def:
      "\<forall>i. \<langle>\<dots>, i(Suc (n - Suc (Suc m))), i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n - Suc (Suc m)), i n\<rangle> \<in> X"
      using Tuple_Extend1 by blast
    from a1 obtain D where "\<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> D \<longleftrightarrow> \<langle>\<dots>, i(n - Suc m), i n\<rangle> \<in> C"
      by blast
    with C_def eq show "\<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n - Suc (Suc m)), i n\<rangle> \<in> X" by auto
  qed
qed 

lemma Tuple_Extend3: "k < n \<Longrightarrow> \<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(k), i(n)\<rangle> \<in> X"
proof -
  assume "k < n"
  then obtain l where "k = n - Suc l" by (metis Suc_diff_Suc diff_diff_cancel less_imp_le)
  with `k < n` show ?thesis using Tuple_Extend2 [of n l] by simp
qed

lemma Tuple_Extend4: "k < n \<Longrightarrow> \<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>i(k), i(n)\<rangle> \<in> X"
proof (cases "k = 0")
  assume "k < n" "k = 0"
  thus ?thesis using Tuple_Extend3 [of k n] by simp
next
  assume "k < n" "k \<noteq> 0"
  then obtain l where "k = Suc l" using not0_implies_Suc by blast
  moreover obtain C where "\<forall>i. \<langle>i(k), i(n), \<langle>\<dots>, i(l)\<rangle>\<rangle> \<in> C \<longleftrightarrow> \<langle>i(k), i(n)\<rangle> \<in> X" using B5 by blast
  moreover then obtain D where "\<forall>u v w. \<langle>u, v, w\<rangle> \<in> D \<longleftrightarrow> \<langle>v, w, u\<rangle> \<in> C" using B6 by blast
  ultimately have "\<forall>i. \<langle>\<dots>, i(k), i(n)\<rangle> \<in> D \<longleftrightarrow> \<langle>i(k), i(n)\<rangle> \<in> X" by simp
  moreover with `k < n` obtain E where "\<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> E \<longleftrightarrow> \<langle>\<dots>, i(k), i(n)\<rangle> \<in> D"
    using Tuple_Extend3 by blast
  ultimately show ?thesis by auto
qed

definition Swap :: "[nat \<Rightarrow> Set, nat, nat] \<Rightarrow> (nat \<Rightarrow> Set)"
where "Swap f n m = (\<lambda>k. if k = n then f(m) else if k = m then f(n) else f(k))"

lemma Double_Swap: "Swap (Swap f n m) n m = f"
unfolding Swap_def by auto

lemma Update_Swap: "Update (Swap f m n) n y = Swap (Update f m y) m n"
unfolding Update_def Swap_def by auto


text{* \textbf{FOMUS workshop extra exercise:} *}

lemma Tuple_Swap: "k < n \<Longrightarrow> (\<exists>C. \<forall>i. \<langle>\<dots>, (Swap i k n)(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n)\<rangle> \<in> X)"
sorry                                                          

lemma Tuple_Swap_Inter: "\<forall>i. \<langle>\<dots>, (Swap i k n)(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n)\<rangle> \<in> X \<Longrightarrow>
  \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, (Swap i k n)(n)\<rangle> \<in> X"
using Double_Swap by metis

lemma Class_Project1: "\<exists>C. \<forall>x y. \<langle>x, y\<rangle> \<in> C \<longleftrightarrow> (\<exists>z. \<langle>x, z\<rangle> \<in> X)" 
--"Class existence for the projection class."
using B4 [of X] B5 [of "dom X"] by simp

lemma Class_Project2: "\<exists>C. \<forall>i. \<langle>\<dots>, i(0)\<rangle> \<in> C \<longleftrightarrow> (\<exists>y. \<langle>\<dots>, (Update i 0 y)(0)\<rangle> \<in> X)"
unfolding Update_def using Ex4_9_b by auto

lemma Class_Project3: "0 < n \<Longrightarrow> \<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C
  \<longleftrightarrow> (\<exists>y. \<langle>\<dots>, (Update i n y)(n)\<rangle> \<in> X)"
proof -
  assume "0 < n"
  then obtain m where "n = Suc m" using not0_implies_Suc by blast
  have "\<exists>C. \<forall>v. \<forall>i. \<langle>\<dots>, i(m), v\<rangle> \<in> C \<longleftrightarrow> (\<exists>y. \<langle>\<dots>, i(m), y\<rangle> \<in> X)"
      using Class_Project1 by blast
    with `n = Suc m` have "\<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> (\<exists>y. \<langle>\<dots>, i(m), y\<rangle> \<in> X)" by auto
  moreover have "\<forall>i. \<forall>y. \<langle>\<dots>, i(m), y\<rangle> =  ToTuple (\<lambda>l. if l = n then y else i(l)) n"
  proof (rule allI, rule allI)
    fix i :: "nat \<Rightarrow> Set"
    fix y
    have "\<langle>\<dots>, i(m)\<rangle> = ToTuple (\<lambda>l. if l = Suc m then y else i l) m"
      using Tuple_Dom [of m i "\<lambda>l. if l = Suc m then y else i l"] by simp
    with `n = Suc m` show "\<langle>\<dots>, i(m), y\<rangle> = ToTuple (\<lambda>l. if l = n then y else i(l)) n"
      by simp
  qed
  ultimately show ?thesis unfolding Update_def by simp
qed

lemma Class_Project4: "k < n \<Longrightarrow> \<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C
  \<longleftrightarrow> (\<exists>y. \<langle>\<dots>, (Update i k y)(n)\<rangle> \<in> X)"
proof -
  assume "k < n"
  then obtain C where C_def:
    "\<forall>i. \<langle>\<dots>, (Swap i k n)(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n)\<rangle> \<in> X"
    using Tuple_Swap by blast
  from `k < n` have "0 < n" by simp
  then obtain D where D_def:
    "\<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> D \<longleftrightarrow> (\<exists>y. \<langle>\<dots>, (Update i n y)(n)\<rangle> \<in> C)"
    using Class_Project3 by blast
  from `k < n` obtain E where "\<forall>i. \<langle>\<dots>, (Swap i k n)(n)\<rangle> \<in> E \<longleftrightarrow> \<langle>\<dots>, i(n)\<rangle> \<in> D"
    using Tuple_Swap by blast
  hence "\<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> E \<longleftrightarrow> \<langle>\<dots>, (Swap i k n)(n)\<rangle> \<in> D" using Tuple_Swap_Inter by fast
  with D_def have "\<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> E \<longleftrightarrow> (\<exists>y. \<langle>\<dots>, (Update (Swap i k n) n y)(n)\<rangle> \<in> C)"
    by simp
  moreover from C_def
    have "\<forall>i. \<forall>y. \<langle>\<dots>, (Update (Swap i k n) n y)(n)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, (Update i k y)(n)\<rangle> \<in> X"
    using Update_Swap by simp
  ultimately show "\<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> (\<exists>y. \<langle>\<dots>, (Update i k y)(n)\<rangle> \<in> X)" by auto
qed

lemma Class_Ex_Subset: "\<exists>C. \<forall>x y. \<langle>x, y\<rangle> \<in> C \<longleftrightarrow> x \<subseteq> y"
proof -
  obtain C1 where C1_def: "\<forall>z x. \<langle>z, x\<rangle> \<in> C1 \<longleftrightarrow> z \<in> x" using B1 by blast
  moreover obtain C2 where C2_def: "\<forall>x z. \<langle>x, z\<rangle> \<in> C2 \<longleftrightarrow> \<langle>z, x\<rangle> \<in> C1" using Ex_4_11_a by blast
  moreover obtain C3 where "\<forall>x y z. \<langle>x, y, z\<rangle> \<in> C3 \<longleftrightarrow> \<langle>x, z\<rangle> \<in> C2" using Ex_4_11_b by blast
  ultimately have a1: "\<forall>x y z. \<langle>x, y, z\<rangle> \<in> C3 \<longleftrightarrow> z \<in> x" by simp
  from C1_def C2_def have "\<forall>y z. \<langle>y, z\<rangle> \<in> Co(C2) \<longleftrightarrow> z \<notin> y" using B3 by simp
  moreover obtain D1 where "\<forall>y z x. \<langle>y, z, x\<rangle> \<in> D1 \<longleftrightarrow> \<langle>y, z\<rangle> \<in> Co(C2)" using B5 by blast
  moreover obtain D2 where "\<forall>x y z. \<langle>x, y, z\<rangle> \<in> D2 \<longleftrightarrow> \<langle>y, z, x\<rangle> \<in> D1" using B6 by blast
  ultimately have "\<forall>x y z. \<langle>x, y, z\<rangle> \<in> D2 \<longleftrightarrow> z \<notin> y" by simp
  with a1 have "\<forall>x y z. \<langle>x, y, z\<rangle> \<in> C3 \<inter> D2 \<longleftrightarrow> z \<in> x \<and> z \<notin> y" using B2 by blast
  moreover have "\<forall>x y. \<langle>x, y\<rangle> \<notin> dom(C3 \<inter> D2) \<longleftrightarrow> \<not>(\<exists>z. \<langle>x, y, z\<rangle> \<in> C3 \<inter> D2)" using B4 by blast
  moreover have "\<forall>x y. \<langle>x, y\<rangle> \<in> Co(dom(C3 \<inter> D2)) \<longleftrightarrow> \<langle>x, y\<rangle> \<notin> dom(C3 \<inter> D2)" using B3 by blast
  ultimately have "\<forall>x y. \<langle>x, y\<rangle> \<in> Co(dom(C3 \<inter> D2)) \<longleftrightarrow> (\<forall>z :: Set. (z \<in> x \<longrightarrow> z \<in> y))" by simp
  thus ?thesis using subset by auto
qed

lemma Class_Ex_Equals1: "\<exists>C. \<forall>x y. \<langle>x, y\<rangle> \<in> C \<longleftrightarrow> x = y"
proof -
  obtain C1 where "\<forall>x y. \<langle>x, y\<rangle> \<in> C1 \<longleftrightarrow> x \<subseteq> y" using Class_Ex_Subset by blast
  moreover obtain C2 where "\<forall>x y. \<langle>x, y\<rangle> \<in> C2 \<longleftrightarrow> \<langle>y, x\<rangle> \<in> C1" using Ex_4_11_a by blast
  ultimately have "\<forall>x y. \<langle>x, y\<rangle> \<in> C1 \<inter> C2 \<longleftrightarrow> x = y" using B2 Prop4_1_a Rep_Set_inject by auto
  thus ?thesis ..
qed

lemma Class_Ex_Antifoundation: "\<exists>C. \<forall>x :: Set. x \<in> C \<longleftrightarrow> x \<in> x"
proof -
  obtain C where "\<forall>x y. \<langle>x, y\<rangle> \<in> C \<longleftrightarrow> x \<in> y" using B1 ..
  moreover obtain D where "\<forall>x y. \<langle>x, y\<rangle> \<in> D \<longleftrightarrow> x = y" using Class_Ex_Equals1 ..
  ultimately have "\<forall>x. x \<in> dom(C \<inter> D) \<longleftrightarrow> (\<exists>y :: Set. x \<in> y \<and> x = y)" using B2 B4 by simp
  moreover have "\<forall>x. x \<in> x \<longleftrightarrow> (\<exists>y :: Set. x \<in> y \<and> x = y)" by simp
  ultimately show ?thesis by blast
qed

lemma Class_Ex_Belongs_CV1: "\<exists>C. \<forall>x :: Set. x \<in> C \<longleftrightarrow> X \<in> x"
proof (cases "\<exists>w :: Set. X = w")
  assume "\<exists>w :: Set. X = w"
  then obtain w :: Set where "X = w" by blast
  hence "\<forall>x. x \<in> {w} \<longleftrightarrow> x = X" using singletonE using pairing by blast 
  then obtain C where "\<forall>x y. \<langle>y, x\<rangle> \<in> C \<longleftrightarrow> y = X" using B5 by metis
  moreover then obtain D where "\<forall>x y. \<langle>y, x\<rangle> \<in> D \<longleftrightarrow> y \<in> x" using B1 by blast
  ultimately have "\<forall>x y. \<langle>y, x\<rangle> \<in> C \<inter> D \<longleftrightarrow> y = X \<and> y \<in> x" using B2 by simp
  then obtain E where "\<forall>x y. \<langle>x, y\<rangle> \<in> E \<longleftrightarrow> y = X \<and> y \<in> x" using Ex_4_11_a by metis
  hence "\<forall>x :: Set. x \<in> dom(E) \<longleftrightarrow> (\<exists>y :: Set. y = X \<and> y \<in> x)" using B4 by simp
  with `X = w` show ?thesis by metis
next
  assume "\<not> (\<exists>w :: Set. X = w)"
  hence "\<forall>x :: Set. X \<notin> x" by (metis CollectI Rep_Set_cases set_predicate_def universe)
  thus ?thesis using empty_set by auto
qed

lemma Class_Ex_Belongs_CV:  
  fixes \<phi> :: FOL_Formula 
  fixes C :: Class
  fixes n :: nat
  assumes "\<phi> = (FBelongs (FConst C) (FVar n))"
  shows   "Class_Ex \<phi> (FOL_MaxVar \<phi>)" 
proof -
  have n: "n = FOL_MaxVar \<phi>" by (simp add: assms)
  have *: "\<exists>C'. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C' \<longleftrightarrow> C \<in> i(n)" using Class_Ex_Belongs_CV1 Tuple_Last by fastforce
  have "\<forall>i. FOL_True \<phi> i \<longleftrightarrow> C \<in> i(n)" using FOL_True.simps FOL_Eval.simps assms by simp
  thus "Class_Ex \<phi> (FOL_MaxVar \<phi>)" unfolding Class_Ex_def using n * by simp
qed

lemma Class_Ex_Belongs_VV: "Class_Ex (FBelongs (FVar n) (FVar m))
  (FOL_MaxVar (FBelongs (FVar n) (FVar m)))"
proof (rule Nat.nat_less_cases [of n m])
  assume "n < m"
  moreover then obtain C where "\<forall>i. \<langle>i(n), i(m)\<rangle> \<in> C \<longleftrightarrow> i(n) \<in> i(m)" using B1 by auto
  ultimately obtain D where "\<forall>i. \<langle>\<dots>, i(m)\<rangle> \<in> D \<longleftrightarrow> i(n) \<in> i(m)" using Tuple_Extend4 by metis
  moreover from `n < m` have "max n m = m" by simp
  ultimately show ?thesis unfolding Class_Ex_def by auto
next
  assume "n = m"
  thus ?thesis unfolding Class_Ex_def using Tuple_Last Class_Ex_Antifoundation by fastforce
next
  assume "m < n"
  moreover then obtain C where "\<forall>i. \<langle>i(m), i(n)\<rangle> \<in> C \<longleftrightarrow> i(n) \<in> i(m)" using B1 Ex_4_11_a by metis
  ultimately obtain D where "\<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> D \<longleftrightarrow> i(n) \<in> i(m)" using Tuple_Extend4 by metis
  moreover from `m < n` have "max n m = n" by simp
  ultimately show ?thesis unfolding Class_Ex_def by auto
qed

lemma Class_Ex_Equals_CC: "Class_Ex (FEquals (FConst c) (FConst d))
  (FOL_MaxVar (FEquals (FConst c) (FConst d)))"
proof (unfold Class_Ex_def, simp, cases "c = d")
  assume "c = d"
  thus "\<exists>C. \<forall>i :: nat \<Rightarrow> Set. i(0) \<in> C \<longleftrightarrow> c = d" using Ex4_9_b by auto
next
  assume "c \<noteq> d"
  thus "\<exists>C. \<forall>i :: nat \<Rightarrow> Set. i(0) \<in> C \<longleftrightarrow> c = d" using empty_set by auto
qed

lemma Class_Ex_Equals_VC: "Class_Ex (FEquals (FVar n) (FConst c))
  (FOL_MaxVar (FEquals (FVar n) (FConst c)))"
proof (unfold Class_Ex_def, simp, cases "\<exists>z :: Set. z = c")
  assume "\<exists>z :: Set. z = c"
  then obtain z :: Set where "z = c" by blast
  hence "\<forall>x. x \<in> {z} \<longleftrightarrow> x = c" using singletonE singletonI pairing by blast 
  moreover obtain C where "\<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> i(n) \<in> {z}" using Tuple_Last by blast
  ultimately show "\<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> i(n) = c" by auto
next
  assume "\<not> (\<exists>z :: Set. z = c)"
  thus "\<exists>C. \<forall>i. \<langle>\<dots>, i(n)\<rangle> \<in> C \<longleftrightarrow> i(n) = c" using empty_set by auto
qed

lemma Class_Ex_Equals_CV: "Class_Ex (FEquals (FConst c) (FVar n))
  (FOL_MaxVar (FEquals (FConst c) (FVar n)))"
using Class_Ex_Equals_VC unfolding Class_Ex_def by (simp, metis)

lemma Class_Ex_Equals_VV: "Class_Ex (FEquals (FVar n) (FVar k))
  (FOL_MaxVar (FEquals (FVar n) (FVar k)))"
proof (unfold Class_Ex_def, simp, cases "n = k")
  assume "n = k"
  thus "\<exists>C. \<forall>i. \<langle>\<dots>, i(max n k)\<rangle> \<in> C \<longleftrightarrow> (Rep_Set (i(n)) = (i(k)))"
    using Ex4_9_b by auto
next
  obtain C where C_def: "\<forall>x y. \<langle>x, y\<rangle> \<in> C \<longleftrightarrow> x = y" using Class_Ex_Equals1 ..
  assume "n \<noteq> k"
  hence "min n k < max n k" by simp
  then obtain D where "\<forall>i. \<langle>\<dots>, i(max n k)\<rangle> \<in> D \<longleftrightarrow> \<langle>i(min n k), i(max n k)\<rangle> \<in> C"
    using Tuple_Extend4 by blast
  with C_def have "\<forall>i. \<langle>\<dots>, i(max n k)\<rangle> \<in> D \<longleftrightarrow> i(min n k) = i(max n k)"
    by blast
  moreover from `n \<noteq> k` have "\<forall>i. i(min n k) = i(max n k) \<longleftrightarrow> i(n) = i(k)"
    by (metis max_def min_def)
  ultimately show "\<exists>C. \<forall>i. \<langle>\<dots>, i(max n k)\<rangle> \<in> C \<longleftrightarrow> (Rep_Set (i(n)) = (i(k)))"
    using Rep_Set_inject by blast
qed

lemma Class_Ex_Equals: "Class_Ex (FEquals x y) (FOL_MaxVar (FEquals x y))"
proof (cases x, cases y, auto simp add: Class_Ex_Equals_VV Class_Ex_Equals_VC Class_Ex_Equals_CV 
                                        Class_Ex_Equals_CC)
  fix n m :: nat
  assume x: "x = FVar n"
  assume y: "y = FVar m"
  show "Class_Ex (FEquals (FVar n) (FVar m)) (max n m)" using Class_Ex_Equals_VV by auto
next 
  fix n :: nat
  fix Y :: Class
  assume "x = FVar n"
  assume "y = FConst Y"
  show "Class_Ex (FEquals (FVar n) (FConst Y)) n" using Class_Ex_Equals_VC by auto
next 
  fix X :: Class
  assume "x = FConst X"
  show "Class_Ex (FEquals (FConst X) y) (FOL_Var y)" by (metis Class_Ex_Equals_CC 
    Class_Ex_Equals_CV FOL_MaxVar.simps(4) FOL_Term.exhaust FOL_Var.simps(2) max_0L)
qed

lemma Class_Ex_Belongs: "Class_Ex (FBelongs x y) (FOL_MaxVar (FBelongs x y))"
proof (cases x, cases y, auto simp add: Class_Ex_Belongs_VV Class_Ex_Belongs_VC Class_Ex_Belongs_CC)
  fix n m:: nat
  assume "x = FVar n"
  assume "y = FVar m"
  show   "Class_Ex (FBelongs (FVar n) (FVar m)) (max n m)" using Class_Ex_Belongs_VV by auto
next
  fix n :: nat
  fix Y :: Class 
  assume "x = FVar n"
  assume "y = FConst Y"
  show "Class_Ex (FBelongs (FVar n) (FConst Y)) n" using Class_Ex_Belongs_VC by auto
next 
  fix X ::Class
  assume "x = FConst X"
  show "Class_Ex (FBelongs (FConst X) y) (FOL_Var y)" by (metis Class_Ex_Belongs_CC 
    Class_Ex_Belongs_CV FOL_MaxVar.simps(3) FOL_Term.exhaust FOL_Var.simps(2) max_0L)
qed    


lemma Class_Ex_And: "\<lbrakk>Class_Ex \<phi> n; Class_Ex \<psi> n\<rbrakk> \<Longrightarrow> Class_Ex (FAnd \<phi> \<psi>) n"
proof -
  assume "Class_Ex \<phi> n"
  then obtain C where ex1: "\<forall>j. \<langle>\<dots>, j(n)\<rangle> \<in> C \<longleftrightarrow> FOL_True \<phi> j"
    unfolding Class_Ex_def by blast
  assume "Class_Ex \<psi> n"
  then obtain D where "\<forall>j. \<langle>\<dots>, j(n)\<rangle> \<in> D \<longleftrightarrow> FOL_True \<psi> j"
    unfolding Class_Ex_def by blast
  with ex1 have "\<forall>j. \<langle>\<dots>, j(n)\<rangle> \<in> C \<inter> D \<longleftrightarrow> (FOL_True \<phi> j \<and> FOL_True \<psi> j)"
    using B2 by blast
  thus ?thesis unfolding Class_Ex_def by auto
qed

lemma Class_Ex_Not: "Class_Ex \<phi> n \<Longrightarrow> Class_Ex (FNot \<phi>) n"
proof -
  assume "Class_Ex \<phi> n"
  then obtain C where "\<forall>j. \<langle>\<dots>, j(n)\<rangle> \<in> C \<longleftrightarrow> FOL_True \<phi> j"
    unfolding Class_Ex_def by blast
  hence "\<forall>j :: nat \<Rightarrow> Set. \<langle>\<dots>, j(n)\<rangle> \<in> Co(C) \<longleftrightarrow> \<not> (FOL_True \<phi> j)"
    using B3 by blast
  thus ?thesis unfolding Class_Ex_def by auto
qed

lemma Class_Ex_Or: "\<lbrakk>Class_Ex \<phi> n; Class_Ex \<psi> n\<rbrakk> \<Longrightarrow> Class_Ex (FOr \<phi> \<psi>) n"
proof -
  assume "Class_Ex \<phi> n"
  hence ex1: "Class_Ex (FNot \<phi>) n" by (rule Class_Ex_Not)
  assume "Class_Ex \<psi> n"
  hence ex2: "Class_Ex (FNot \<psi>) n" by (rule Class_Ex_Not)
  from ex1 ex2 have ex3: "Class_Ex (FAnd (FNot \<phi>) (FNot \<psi>)) n" by (rule Class_Ex_And)
  hence "Class_Ex (FNot (FAnd (FNot \<phi>) (FNot \<psi>))) n" by (rule Class_Ex_Not)
  thus ?thesis unfolding Class_Ex_def by simp
qed

lemma Class_Ex_Imp: "\<lbrakk>Class_Ex \<phi> n; Class_Ex \<psi> n\<rbrakk> \<Longrightarrow> Class_Ex (FImp \<phi> \<psi>) n"
proof -
  assume "Class_Ex \<phi> n"
  hence ex1: "Class_Ex (FNot \<phi>) n" by (rule Class_Ex_Not)
  assume "Class_Ex \<psi> n"
  with ex1 have "Class_Ex (FOr (FNot \<phi>) \<psi>) n" by (rule Class_Ex_Or)
  thus ?thesis unfolding Class_Ex_def by simp
qed

lemma Class_Ex_Iff: "\<lbrakk>Class_Ex \<phi> n; Class_Ex \<psi> n\<rbrakk> \<Longrightarrow> Class_Ex (FIff \<phi> \<psi>) n"
proof -
  assume ex1: "Class_Ex \<phi> n"
  assume ex2: "Class_Ex \<psi> n"
  from ex1 ex2 have ex3: "Class_Ex (FImp \<phi> \<psi>) n" by (rule Class_Ex_Imp)
  from ex2 ex1 have "Class_Ex (FImp \<psi> \<phi>) n" by (rule Class_Ex_Imp)
  with ex3 have "Class_Ex (FAnd (FImp \<phi> \<psi>) (FImp \<psi> \<phi>)) n" by (rule Class_Ex_And)
  thus ?thesis unfolding Class_Ex_def by auto
qed

lemma Class_Ex_Irr: "n > FOL_MaxVar \<phi> \<Longrightarrow> FOL_True (FEx n \<phi>) i \<longleftrightarrow> FOL_True \<phi> i"
proof -
  assume "FOL_MaxVar \<phi> < n"
  hence "\<forall>y. \<forall>k \<le> FOL_MaxVar \<phi>. i(k) = (Update i n y)(k)" unfolding Update_def by simp
  hence "\<forall>y. FOL_True \<phi> i \<longleftrightarrow> FOL_True \<phi> (Update i n y)" using FOL_MaxVar_Dom by simp
  thus ?thesis by simp
qed

lemma Class_Ex_Ex: "Class_Ex \<phi> (FOL_MaxVar \<phi>) \<Longrightarrow> Class_Ex (FEx n \<phi>) (FOL_MaxVar (FEx n \<phi>))"
proof (cases "FOL_MaxVar \<phi> < n")
  assume "Class_Ex \<phi> (FOL_MaxVar \<phi>)"
  moreover assume "FOL_MaxVar \<phi> < n"
  ultimately show "Class_Ex (FEx n \<phi>) (FOL_MaxVar (FEx n \<phi>))"
    unfolding Class_Ex_def using Class_Ex_Irr by simp
next
  assume "Class_Ex \<phi> (FOL_MaxVar \<phi>)"
  then obtain D where D_def: "\<forall>i. \<langle>\<dots>, i(FOL_MaxVar \<phi>)\<rangle> \<in> D \<longleftrightarrow> FOL_True \<phi> i"
    unfolding Class_Ex_def by blast
  assume "\<not> FOL_MaxVar \<phi> < n"
  then consider "n = 0 \<and> FOL_MaxVar \<phi> = 0" | "0 < n \<and> FOL_MaxVar \<phi> = n" | "n < FOL_MaxVar \<phi>"
    by linarith
  hence "\<exists>C. \<forall>i. \<langle>\<dots>, i(FOL_MaxVar \<phi>)\<rangle> \<in> C \<longleftrightarrow> (\<exists>y. \<langle>\<dots>, (Update i n y)(FOL_MaxVar \<phi>)\<rangle> \<in> D)"
    using Class_Project2 Class_Project3 Class_Project4 by (cases, simp_all)
  with D_def show ?thesis unfolding Class_Ex_def by simp
qed

lemma Class_Ex_All: "Class_Ex \<phi> (FOL_MaxVar \<phi>) \<Longrightarrow> Class_Ex (FAll n \<phi>) (FOL_MaxVar (FAll n \<phi>))"
proof -
  assume "Class_Ex \<phi> (FOL_MaxVar \<phi>)"
  hence "Class_Ex (FNot \<phi>) (FOL_MaxVar \<phi>)" by (rule Class_Ex_Not)
  hence "Class_Ex (FEx n (FNot \<phi>)) (FOL_MaxVar (FEx n \<phi>))" using Class_Ex_Ex
    by (metis FOL_MaxVar.simps(10) FOL_MaxVar.simps(6))
  hence "Class_Ex (FNot (FEx n (FNot \<phi>))) (FOL_MaxVar (FAll n \<phi>))" using Class_Ex_Not by simp
  thus ?thesis unfolding Class_Ex_def by auto
qed

theorem Class_Existence: "Class_Ex \<phi> (FOL_MaxVar \<phi>)"
-- "For every FOL_Formula \<phi> there exists a class which contains exactly those n-tuples which 
    satisfy \<phi>, where n is the largest set-variable index appearing in \<phi>."
proof (induct \<phi>, auto simp add: Class_Ex_True Class_Ex_False  Class_Ex_Belongs  Class_Ex_Equals
                                Class_Ex_And  Class_Ex_Mono2  Class_Ex_Or       Class_Ex_Not  
                                Class_Ex_Imp  Class_Ex_Iff)
  fix x1 x2::FOL_Term
  show "Class_Ex (FBelongs x1 x2) (max (FOL_Var x1) (FOL_Var x2))" using Class_Ex_Belongs by auto
  show "Class_Ex (FEquals x1 x2) (max (FOL_Var x1) (FOL_Var x2))"  using Class_Ex_Equals by auto
next
  fix n  :: nat
  fix \<phi>  :: FOL_Formula 
  assume IH: "Class_Ex \<phi> (FOL_MaxVar \<phi>)"
  thus "Class_Ex (FEx n \<phi>) (FOL_MaxVar \<phi>)" using Class_Ex_Ex FOL_MaxVar.simps(10) by auto
  from IH show "Class_Ex (FAll n \<phi>) (FOL_MaxVar \<phi>)" using Class_Ex_All FOL_MaxVar.simps(11) by auto
qed
  
end