theory FOL_substitution
imports FOL_formula
begin

section{*FOL Substitution *}
text{* Here we we set up substitution for FOL_Formulas. The goal is the Class Existence Theorem 
       of the next section, which says that FOL_Formulas define classes.*}

primrec FOL_MaxVar2 :: "FOL_Formula \<Rightarrow> nat"
--"In contrast to FOL_MaxVar, FOL_MaxVar2 looks at every variable even the quantified ones."
where
  "FOL_MaxVar2 FTrue = 0"
  | "FOL_MaxVar2 FFalse = 0"
  | "FOL_MaxVar2 (FBelongs x y) = max (FOL_Var x) (FOL_Var y)"
  | "FOL_MaxVar2 (FEquals x y) = max (FOL_Var x) (FOL_Var y)"
  | "FOL_MaxVar2 (FAnd \<phi> \<psi>) = max (FOL_MaxVar2 \<phi>) (FOL_MaxVar2 \<psi>)"
  | "FOL_MaxVar2 (FNot \<phi>) = FOL_MaxVar2 \<phi>"
  | "FOL_MaxVar2 (FOr \<phi> \<psi>) = max (FOL_MaxVar2 \<phi>) (FOL_MaxVar2 \<psi>)"
  | "FOL_MaxVar2 (FImp \<phi> \<psi>) = max (FOL_MaxVar2 \<phi>) (FOL_MaxVar2 \<psi>)"
  | "FOL_MaxVar2 (FIff \<phi> \<psi>) = max (FOL_MaxVar2 \<phi>) (FOL_MaxVar2 \<psi>)"
  | "FOL_MaxVar2 (FEx n \<phi>) = max n (FOL_MaxVar2 \<phi>)"
  | "FOL_MaxVar2 (FAll n \<phi>) = max n (FOL_MaxVar2 \<phi>)"

text{* We now define Finite partial functions (Fpf) from nat to nat, as in John Harrison's "Handbook of Practical 
       Logic and Automated Reasoning", and prove some basic facts about them. *}
 
datatype Fpf = Nil | Elem nat nat Fpf 
(*    Examples:
      Nil ~ Id\<^sub>n\<^sub>a\<^sub>t
      Elem 10 20 Nil ~ (10 \<mapsto> 20)Id\<^sub>n\<^sub>a\<^sub>t 
      Elem 10 20 (Elem 30 40 Nil) ~ (10 \<mapsto> 20) (30 \<mapsto> 40)Id\<^sub>n\<^sub>a\<^sub>t
      Elem 10 30 (Elem 10 20 Nil) ~ (10 \<mapsto> 30) (10 \<mapsto> 20)Id\<^sub>n\<^sub>a\<^sub>t = (1 \<mapsto> 3)Id\<^sub>n\<^sub>a\<^sub>t*)


(* Fp function application *)
primrec assoc :: "[Fpf, nat] \<Rightarrow> nat" 
where
  "assoc Nil k = k"
| "assoc (Elem x y rest) k = (if x = k then y else (assoc rest k))"

(* associable lst k = True \<longleftrightarrow> k occurs in any of the Elem-blocks
as the first or second field 
Example associable (Elem 10 20 (Elem 30 40 Nil)) 30 = True
        associable (Elem 10 20 (Elem 30 40 Nil)) 50 = False
*)
primrec associable :: "[Fpf, nat] \<Rightarrow> bool"
where 
  "associable Nil k = False"
| "associable (Elem x y rest) k = ((x = k) \<or> (associable rest k) \<or> (y = k))"

(* Substitution of all variables  with their image under an fpf
   which is itself if it does not occur in the domain. *) 
primrec subst_t :: "[FOL_Term, Fpf] \<Rightarrow> FOL_Term"
where  
  "subst_t (FVar n) fpf = FVar (assoc fpf n)"
| "subst_t (FConst y) fpf = FConst y" 

(* Yields a variable that does not occur in a given fpf  *)
primrec alpha_convert_0 :: "[Fpf] \<Rightarrow> nat"
where
  "alpha_convert_0 Nil = 0"
| "alpha_convert_0 (Elem x y rest) = (max (Suc x) (max (Suc y) (alpha_convert_0 rest)))"

(* Yields a variable that does neither occur in a given fpf nor in a given FOL_Formula *)
definition alpha_convert :: "[FOL_Formula, Fpf] \<Rightarrow> nat"
where
  "alpha_convert p f = (max (Suc (FOL_MaxVar2 p)) (alpha_convert_0 f))"

(* Substitution of all variables  with their image under an fpf.
   Gives new names to quantified variables even if it is not necessary
   because that makes some of the following theorems easier to prove. *)
fun subst_f :: "[FOL_Formula, Fpf] \<Rightarrow> FOL_Formula"
where 
  "subst_f FTrue fpf = FTrue"
| "subst_f FFalse fpf = FFalse"
| "subst_f (FBelongs x y) fpf = (FBelongs (subst_t x fpf) (subst_t y fpf))"
| "subst_f (FEquals x y) fpf = (FEquals (subst_t x fpf) (subst_t y fpf))"
| "subst_f (FAnd p q) fpf = (FAnd (subst_f p fpf) (subst_f q fpf))"
| "subst_f (FOr p q) fpf = (FOr (subst_f p fpf) (subst_f q fpf))"
| "subst_f (FNot p) fpf = (FNot (subst_f p fpf))"
| "subst_f (FImp p q) fpf = (FImp (subst_f p fpf) (subst_f q fpf))"
| "subst_f (FIff p q) fpf = (FIff (subst_f p fpf) (subst_f q fpf))"
| "subst_f (FEx n q) fpf = (FEx (alpha_convert (FEx n q) fpf) 
                                (subst_f q (Elem n (alpha_convert (FEx n q) fpf) fpf)))"
| "subst_f (FAll n q) fpf = (FAll (alpha_convert  (FEx n q) fpf) 
                                  (subst_f q (Elem n (alpha_convert (FEx n q) fpf) fpf)))"
 
(* Updates an intepretation i :: nat \<Rightarrow> Set according to a given Fpf f, i.e.
   replaces i(n) with i ( f(n) ) for every n. *)
definition Update2 :: "[nat \<Rightarrow> Set, Fpf] \<Rightarrow> (nat \<Rightarrow> Set)"
where "Update2 i fpf k =  i (assoc fpf k) "

(* substitution of a single variable. Just convenience definitions for proof
  of ex_definable_lemma in Class_Comprehension.thy. *)
definition single_subst_t :: "[FOL_Term, nat, nat] \<Rightarrow> FOL_Term"
where "single_subst_t x i j = subst_t x (Elem i j Nil)"

definition single_subst_f :: "[FOL_Formula, nat, nat] \<Rightarrow> FOL_Formula"
where "single_subst_f x i j = subst_f x (Elem i j Nil)"

lemma MaxVar_comp: "FOL_MaxVar \<phi> \<le> FOL_MaxVar2 \<phi>"
by (induct \<phi>, auto)

(* Same as FOL_MaxVar_Dom but with FOL_MaxVar2 instead of FOL_MaxVar *)
lemma FOL_MaxVar2_Dom: "\<forall>i. \<forall>j. (\<forall>k \<le> FOL_MaxVar2 \<phi>. i(k) = j(k)) \<longrightarrow> FOL_True \<phi> i \<longleftrightarrow> FOL_True \<phi> j"
using FOL_MaxVar_Dom MaxVar_comp le_trans by blast

(* Convenience lemma *)
lemma FOL_MaxVar2_Dom_For_Use: 
"(\<And>k. k \<le> FOL_MaxVar2 \<phi> \<Longrightarrow> i(k) = j(k)) \<Longrightarrow> FOL_True \<phi> i \<longleftrightarrow> FOL_True \<phi> j"
using FOL_MaxVar2_Dom by blast

(* Facts about updates.*)

lemma Update_lemma_0: "Update2 i Nil k = (i k)"
by (metis Update2_def assoc.simps(1)) 

lemma Update_lemma_0': "Update2 i Nil = i"
using Update_lemma_0 Update2_def by auto

lemma Update_lemma_1: "Update2 i (Elem k x2 rest) k = (i x2)"
by (metis Update2_def assoc.simps(2))

lemma Update_lemma_2: "k \<noteq> l \<Longrightarrow> Update2 i (Elem k x2 rest) l = (Update2 i rest) l"
by (metis Update2_def assoc.simps(2))

(* Relation of Update to Update2  *)
lemma Update_lemma_3: "(Update (Update2 i fpf) x (i y)) = (Update2 i (Elem x y fpf))"
proof -
  have "(Update2 i (Elem x y fpf)) = 
   (\<lambda> k::nat. if x = k then (i y) else (Update2 i fpf) k)" using Update_lemma_2 Update_lemma_1 by auto
  also have "\<dots> = (Update (Update2 i fpf) x (i y))" using Update_def by auto 
  finally show ?thesis by auto
qed 

(* Update and Update2 "commute" if the variable that is replaced by Update 
   does not occur in the fpf used by Update2 *)
lemma Update_lemma_4: 
"\<And>i. \<not> associable fpf x' \<Longrightarrow> (Update2 (Update i x' y) fpf) = (Update (Update2 i fpf) x' y)"
proof (induct fpf)
  fix i
  assume "\<not> associable Nil x'"
  have "Update2 (Update i x' y) Nil = Update i x' y" using Update_lemma_0  by auto
  then show "Update2 (Update i x' y) Nil = Update (Update2 i Nil) x' y" 
  using Update_lemma_0' by auto
  next
  fix x1 x2 fpf i
  assume iasm: "\<And>i. (\<not> associable fpf x' \<Longrightarrow> Update2 (Update i x' y) fpf = Update (Update2 i fpf) x' y)"
  assume v: "\<not> associable (Elem x1 x2 fpf) x'"
  then have "\<not> associable fpf x'" by auto
  from v have w: "x' \<noteq> x1" by auto
  from v have w2: "x' \<noteq> x2" by auto
  have "Update2 (Update i x' y) (Elem x1 x2 fpf) = 
  (Update (Update2 (Update i x' y) fpf) x1 ((Update i x' y) x2))" using Update_lemma_3  by auto
  also have "\<dots> =
  (Update (Update (Update2 i fpf) x' y) x1 ((Update i x' y) x2))" using iasm v by auto
  also have "\<dots> =
  (Update (Update (Update2 i fpf) x' y) x1 (i x2))" using w2 Update_def by auto
  also have "\<dots> =
  (Update (Update (Update2 i fpf) x' y) x1 (i x2))" using w2 Update_def by auto
  then have "\<dots> =
  (Update (Update (Update2 i fpf) x1 (i x2)) x' y)" using w Update_def by auto
  also have "\<dots> = 
  (Update (Update2 i (Elem x1 x2 fpf)) x' y)" using Update_lemma_3 by auto
  finally show "Update2 (Update i x' y) (Elem x1 x2 fpf) = Update (Update2 i (Elem x1 x2 fpf)) x' y"
  .
qed

(* facts about associable *)

lemma associable_0: "\<And>x. associable fpf x \<Longrightarrow> x < (alpha_convert_0 fpf)"
by (induct fpf , auto, fastforce)

lemma associable_1: "\<not> associable fpf (alpha_convert (FEx x1 \<phi>) fpf)"
using associable_0 alpha_convert_def max.cobounded2 not_less by fastforce 

(* Technical lemmas used in the proof of subst_lemma*)
lemma subst_help_lemma_1: "\<And> x1 \<phi> y. x' = (alpha_convert (FEx x1 \<phi>) fpf) \<Longrightarrow> (Update2 (Update i x' y) fpf) x' = y"
using Update_def Update_lemma_4 associable_1 by auto

lemma subst_help_lemma_2:
assumes "x' = alpha_convert (FEx x1 \<phi>) fpf"
shows "FOL_True \<phi> (Update (Update (Update2 i fpf) x' y) x1 y) = 
       FOL_True \<phi> (Update (Update2 i fpf) x1 y)"
using Update_def alpha_convert_def assms
by (simp add: FOL_MaxVar2_Dom Suc_n_not_le_n max_def) 

(* Substitution of variables in a formula can be replaced by updating the interpretation
   and vice versa. *)

(* TO DO: Write the proof below in Isar *) 
lemma substitution_lemma: "\<And> fpf i. (FOL_True (subst_f \<phi> fpf) i) =  FOL_True \<phi> (Update2 i fpf)"
apply(induct \<phi>)
apply(simp)+
apply (metis FOL_Eval.simps(1) FOL_Eval.simps(2) FOL_Term.exhaust Update2_def subst_t.simps(1) 
             subst_t.simps(2))
apply(simp)
apply (metis FOL_Eval.simps(1) FOL_Eval.simps(2) FOL_Term.exhaust Update2_def subst_t.simps(1) 
             subst_t.simps(2))
apply(simp)
apply(simp)
apply(simp)
apply(simp)
apply(simp)
proof -
  fix x1 \<phi> fpf i
  show " (\<And>fpf i. FOL_True (subst_f \<phi> fpf) i = FOL_True \<phi> (Update2 i fpf)) \<Longrightarrow>
       FOL_True (subst_f (FEx x1 \<phi>) fpf) i = FOL_True (FEx x1 \<phi>) (Update2 i fpf)"
  proof -
    def "x'" \<equiv> "(alpha_convert (FEx x1 \<phi>) fpf)"
    assume iasm: "(\<And>fpf i. FOL_True (subst_f \<phi> fpf) i = FOL_True \<phi> (Update2 i fpf))"
    have "FOL_True (subst_f (FEx x1 \<phi>) fpf) i = 
       FOL_True (FEx x' (subst_f \<phi> (Elem x1 x' fpf))) i" 
    using x'_def by auto
    also have "\<dots> =
      (\<exists> y::Set. FOL_True (subst_f \<phi> (Elem x1 x' fpf)) (Update i x' y))" by auto
    also have "\<dots> =
      (\<exists> y::Set. FOL_True \<phi> (Update2 (Update i x' y) (Elem x1 x' fpf)))" using iasm by auto
    also have "\<dots> =
      (\<exists> y::Set. FOL_True \<phi> (Update (Update2 (Update i x' y) fpf) x1 
                                    ((Update2 (Update i x' y) fpf) x')))"
    by (metis Update_def Update_lemma_3 subst_help_lemma_1 x'_def)
    also have "\<dots> =
      (\<exists> y::Set. FOL_True \<phi> (Update (Update2 (Update i x' y) fpf) x1 y))"
    using subst_help_lemma_1 x'_def by auto
    also have "\<dots> =
      (\<exists> y::Set. FOL_True \<phi> (Update (Update (Update2 i fpf) x' y) x1 y))"
    by (simp add: Update_lemma_4 associable_1 x'_def)
    also have "\<dots> = 
      (\<exists> y::Set. FOL_True \<phi> (Update (Update2 i fpf) x1 y))"
    using subst_help_lemma_2 x'_def by auto
    also have "\<dots> = 
      FOL_True (FEx x1 \<phi>) (Update2 i fpf) " by auto
    finally show ?thesis .
   qed
  next
   fix x1 \<phi> fpf i
  show " (\<And>fpf i. FOL_True (subst_f \<phi> fpf) i = FOL_True \<phi> (Update2 i fpf)) \<Longrightarrow>
       FOL_True (subst_f (FAll x1 \<phi>) fpf) i = FOL_True (FAll x1 \<phi>) (Update2 i fpf)"
  proof -
    def "x'" \<equiv> "(alpha_convert (FEx x1 \<phi>) fpf)"
    assume iasm: "(\<And>fpf i. FOL_True (subst_f \<phi> fpf) i = FOL_True \<phi> (Update2 i fpf))"
    have "FOL_True (subst_f (FAll x1 \<phi>) fpf) i = 
       FOL_True (FAll x' (subst_f \<phi> (Elem x1 x' fpf))) i" 
    using x'_def by auto
    also have "\<dots> =
      (\<forall> y::Set. FOL_True (subst_f \<phi> (Elem x1 x' fpf)) (Update i x' y))" by auto
    also have "\<dots> =
      (\<forall> y::Set. FOL_True \<phi> (Update2 (Update i x' y) (Elem x1 x' fpf)))" using iasm by auto
    also have "\<dots> =
      (\<forall> y::Set. FOL_True \<phi> (Update (Update2 (Update i x' y) fpf) x1 
                                     ((Update2 (Update i x' y) fpf) x')))"
    by (metis Update_def Update_lemma_3 subst_help_lemma_1 x'_def)
    also have "\<dots> =
      (\<forall> y::Set. FOL_True \<phi> (Update (Update2 (Update i x' y) fpf) x1 y))"
    using subst_help_lemma_1 x'_def by auto
    also have "\<dots> =
      (\<forall> y::Set. FOL_True \<phi> (Update (Update (Update2 i fpf) x' y) x1 y))"
    by (simp add: Update_lemma_4 associable_1 x'_def)
    also have "\<dots> = 
      (\<forall> y::Set. FOL_True \<phi> (Update (Update2 i fpf) x1 y))"
    using subst_help_lemma_2 x'_def by auto
    also have "\<dots> = 
      FOL_True (FAll x1 \<phi>) (Update2 i fpf) " by auto
    finally show ?thesis .
  qed
qed  


(* Similar to subst_lemma only replacing a single variable. *)
lemma single_subst_lemma: "\<And> k l i. FOL_True (single_subst_f \<phi> k l) i = 
                           FOL_True \<phi> (Update i k (i l))"
using FOL_MaxVar_Dom Update2_def Update_def single_subst_f_def substitution_lemma by auto


end