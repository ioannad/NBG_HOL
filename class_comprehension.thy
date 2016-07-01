theory class_comprehension
imports FOL_substitution
begin

section{* Class Comprehension *}
text{* The goal of this section is to prove Mendelson's ``Class Existence Theorem'', which
       ensures that FOL-definable classes exist. This we see as a class comprehension principle,
       which leads to the set comprehension axiom (not axiom schema).*} 
 
named_theorems defining
declare Class_Existence [defining]

definition definable :: "(Set \<Rightarrow> bool) \<Rightarrow> bool" where
  "definable f == \<exists>\<phi>. \<forall>i. FOL_True \<phi> i \<longleftrightarrow> f(i(0))"

primrec take_domain_rep :: "[nat, Class] \<Rightarrow> Class" where
  "take_domain_rep 0 s = s" |
  "take_domain_rep (Suc n) s =  take_domain_rep n (dom s)"

primrec const_func :: "[Set, nat] \<Rightarrow> Set" where
  "const_func s 0 = s" |
  "const_func s (Suc n) = s"

lemma take_domain_rep_lemma: 
  shows "\<And>C. \<langle>\<dots>, i(n)\<rangle> \<in> C \<Longrightarrow> i(0) \<in> take_domain_rep n C"
proof (induct n)
  show "\<And>C.  \<langle>\<dots>, i(0)\<rangle> \<in> C \<Longrightarrow> (i 0) \<in> take_domain_rep 0 C" by auto
  next
  show "\<And> n. (\<And>C. (\<langle>\<dots>, i(n)\<rangle> \<in> C) \<Longrightarrow> (i 0) \<in> take_domain_rep n C )
    \<Longrightarrow> (\<And>C.  \<langle>\<dots>, i(Suc n)\<rangle> \<in> C \<Longrightarrow> (i 0) \<in> take_domain_rep (Suc n) C)"
    using B4 by auto
qed

lemma take_domain_rep_lemma2: 
  shows "\<And>C. (\<exists> i. i(0) = x \<and>  \<langle>\<dots>, i(n)\<rangle> \<in> C) \<longleftrightarrow> x \<in> take_domain_rep n C"
proof (induct n, simp_all)
  show "\<And>C. (\<exists> i. i(0) = x \<and> i(0) \<in> C) \<longleftrightarrow> x \<in> C" by auto
next  
  fix n
  assume assm: "(\<And>C. (\<exists> i. i(0) = x \<and>  \<langle>\<dots>, i(n)\<rangle> \<in> C) \<longleftrightarrow> x \<in> take_domain_rep n C)"
    show "(\<And>C. (\<exists> i. i(0) = x \<and>  \<langle>\<dots>, i(n), i(Suc n)\<rangle> \<in> C) \<longleftrightarrow> x \<in> take_domain_rep n (dom C))"
  proof (rule iffI)
    fix C
    assume "\<exists>i. i(0)=x \<and>  \<langle>\<dots>, i(n), i (Suc n)\<rangle> \<in> C"  (* left hand side *)
    thus "x \<in> take_domain_rep n (dom C)" using B4 take_domain_rep_lemma by blast 
  next
    fix C
    assume assm1: "x \<in> take_domain_rep n (dom C)"
    show "\<exists>i. i(0)=x \<and>  \<langle>\<dots>, i(n), i(Suc n)\<rangle> \<in> C" 
    proof -
      have "x \<in> take_domain_rep n (dom C)" using assm1 by simp
      then have "\<exists> i. i(0) = x \<and>  \<langle>\<dots>, i(n)\<rangle> \<in> (dom C)" using assm by simp 
      then obtain i where i_def: " i(0) = x \<and>  \<langle>\<dots>, i(n)\<rangle> \<in> (dom C)" ..
      then have "(\<exists> v::Set.  \<langle>\<dots>, i(n), v\<rangle> \<in> C)" using B4 by auto
      then obtain v where " \<langle>\<dots>, i(n), v\<rangle> \<in> C" by auto  
      then have "((Update i (Suc n) v) 0) = x \<and>  \<langle>\<dots>, (Update i (Suc n) v)(Suc n)\<rangle> \<in> C "
        using i_def by (metis ToTuple.simps(2) Tuple_Dom Update_def Zero_not_Suc lessI 
          linorder_not_less)
      then show "\<exists> i. i(0) = x \<and>  \<langle>\<dots>, i(n), i (Suc n)\<rangle> \<in> C" by auto
    qed
  qed
qed

lemma definable_f_property: 
assumes "definable f"
shows "\<exists>C::Class. \<forall>x. x \<in> C \<longleftrightarrow> (f x)" 
proof -
  from assms have "\<exists>\<phi>. \<forall>i. FOL_True \<phi> i \<longleftrightarrow> f(i(0))" unfolding definable_def by auto
  then obtain \<phi> where phi_def: "\<forall>i. FOL_True \<phi> i \<longleftrightarrow> f(i(0))" ..
  have "Class_Ex \<phi> (FOL_MaxVar \<phi>)" by (rule Class_Existence)
  then have "\<exists>C. \<forall>i. \<langle>\<dots>, i(FOL_MaxVar \<phi>)\<rangle> \<in> C \<longleftrightarrow> FOL_True \<phi> i" unfolding Class_Ex_def .
  then obtain C where C_def: "\<forall> i.  \<langle>\<dots>, i(FOL_MaxVar \<phi>)\<rangle> \<in> C \<longleftrightarrow> FOL_True \<phi> i" ..
  obtain D where D_def: "D == take_domain_rep (FOL_MaxVar \<phi>) C" by auto
  have "\<forall> x. x \<in> D \<longleftrightarrow> (f x)"
  proof  
     fix x 
     show "x \<in> D \<longleftrightarrow> (f x)"
     proof 
       show "x \<in> D \<Longrightarrow> f x" by (metis C_def D_def take_domain_rep_lemma2 phi_def) 
       next
       show "f x \<Longrightarrow> x \<in> D" using phi_def C_def D_def take_domain_rep_lemma by fastforce
    qed
  qed
  then show "\<exists>C::Class. \<forall>x. x \<in> C \<longleftrightarrow> (f x)" by (rule exI)
qed                                                                                                   

lemma class_comprehension_uniqueness:
  shows "\<lbrakk>\<forall>x. x \<in> C \<longleftrightarrow> (f x); \<forall>x. x \<in> D \<longleftrightarrow> (f x)\<rbrakk> \<Longrightarrow> C = D"
using extensionality by blast

text{* Classes from non-definable meta-classes are empty. *}

definition class_comprehension :: "(Set \<Rightarrow> bool) \<Rightarrow> Class" where
  "(class_comprehension f) == if (definable f) 
                              then (THE C::Class. \<forall> x::Set. x \<in> C \<longleftrightarrow> (f x))
                              else \<emptyset>"

lemma class_comprehension_welldefined[defining]: 
assumes"definable(f)"
shows "\<exists>! C. \<forall> x. x \<in> C \<longleftrightarrow> f(x)" 
proof -
  from assms obtain D where D_def: "\<forall>x. x \<in> D \<longleftrightarrow> f(x)" using definable_f_property by auto
  then have "\<And>C. (\<forall> x. x \<in> C = f x) \<Longrightarrow> C = D" by (simp add: set_extensionality)  
  with D_def  show ?thesis by blast
qed

lemma class_comprehension_property:
  assumes "definable f"
  shows "\<forall> x::Set. x \<in> (class_comprehension f) \<longleftrightarrow> (f x)"
proof -
from assms have blurp: "(class_comprehension f) = (THE C::Class. \<forall> x::Set. x \<in> C \<longleftrightarrow> (f x))" 
    unfolding class_comprehension_def by simp
from assms have "\<exists>! C. \<forall> x. x \<in> C \<longleftrightarrow> f(x)" by (rule class_comprehension_welldefined)
then show "(\<forall> x::Set. x \<in> (class_comprehension f) \<longleftrightarrow> (f x))" unfolding blurp by (rule theI')
qed

lemma class_comprehensionE:
 fixes f :: "Set \<Rightarrow> bool" 
   and c :: "Set"
 assumes "c \<in> (class_comprehension f)"
 shows "definable f" "f c"
proof -
  show "definable f" by  (metis empty_set assms class_comprehension_def)
  then have "\<forall> x:: Set. x \<in> (class_comprehension f) \<longleftrightarrow> f x" by (rule class_comprehension_property)
  then show "f c" using assms by auto 
qed

lemma class_comprehensionI:
 fixes f :: "Set \<Rightarrow> bool" 
   and c :: "Set"
 assumes "definable f" "f c"
 shows "c \<in> (class_comprehension f)"
by (simp add: assms(1) assms(2) class_comprehension_property)

syntax
  "_class_comprehension"  :: "pttrn \<Rightarrow> bool => Class"        ("(1{_ \<bar> _})")

(* Because "|" also means "or", Isabelle confuses the  {x | \<phi>} 
             with that of a singleton. Therefore we use \<bar>. *)

translations
  "{x \<bar> P}" \<rightleftharpoons> "CONST class_comprehension (\<lambda>x. P)"

(* closure properties of definable *)

lemma true_definable[defining]: "definable (\<lambda> x. True)"
using FOL_True.simps(1) definable_def by blast

lemma not_definable[defining]: 
assumes "definable P" 
shows "definable (\<lambda> x. \<not> P(x))"
by (metis FOL_True.simps(7) assms definable_def)

lemma false_definable[defining]: "definable (\<lambda> x. False)"
using FOL_True.simps(2) definable_def by blast

lemma and_definable[defining]: 
assumes "definable P" and "definable Q"
shows "definable (\<lambda> x. P(x) \<and> Q(x))"
unfolding definable_def 
proof -
  from assms obtain A  where
    A_def: "(\<forall>i. FOL_True A i \<longleftrightarrow> P(i(0)))" 
  unfolding definable_def by auto
  from assms obtain B where
    B_def: "(\<forall>i. FOL_True B i \<longleftrightarrow> Q(i(0)))"
  unfolding definable_def by auto
  from A_def and B_def have  
    "(\<forall>i. FOL_True (FAnd A B) i \<longleftrightarrow> (P(i(0)) \<and> Q(i(0))))" by auto
  then show "\<exists>\<phi>. (\<forall>i. FOL_True \<phi> i = (P (i 0) \<and> Q (i 0)))" by (rule exI)
qed

lemma or_definable[defining]: 
assumes "definable P" and "definable Q"
shows "definable (\<lambda> x. P(x) \<or> Q(x))"
proof -
  from \<open>definable P\<close> have dnP: "definable (\<lambda> x. \<not> P(x))" by (rule not_definable)
  from \<open>definable Q\<close> have dnQ: "definable (\<lambda> x. \<not> Q(x))" by (rule not_definable)
  from dnP and dnQ have "definable (\<lambda> x. \<not> P(x) \<and> \<not> Q(x))" by (rule and_definable)
  then have "definable (\<lambda> x. \<not> (\<not> P(x) \<and> \<not> Q(x)))" by (rule not_definable)
  then show ?thesis by simp   
qed

lemma imp_definable[defining]: 
assumes "definable P" and "definable Q"
shows "definable (\<lambda> x. P(x) \<longrightarrow> Q(x))"
proof -
  from \<open>definable P\<close> have dnP: "definable (\<lambda> x. \<not> P(x))" by (rule not_definable)
  from dnP and \<open>definable Q\<close> have "definable (\<lambda> x. \<not> P(x) \<or> Q(x))" by (rule or_definable)
  then show ?thesis by simp   
qed

lemma iff_definable[defining]: 
assumes "definable P" and "definable Q"
shows "definable (\<lambda> x. P(x) \<longleftrightarrow> Q(x))"
proof-
  have 0: "\<And>x. (P(x) \<longrightarrow> Q(x)) \<and> (Q(x) \<longrightarrow> P(x)) =  P(x) \<longleftrightarrow> Q(x)" by auto
  from assms have 1: "definable (\<lambda> x. P(x) \<longrightarrow> Q(x))" by (rule imp_definable)
  from \<open>definable Q\<close> \<open>definable P\<close> have 2: "definable (\<lambda> x. Q(x) \<longrightarrow> P(x))" by (rule imp_definable)
  from 1 and 2 have "definable (\<lambda> x. (P(x) \<longrightarrow> Q(x)) \<and> (Q(x) \<longrightarrow> P(x)))"  by (rule and_definable)
  then show "definable (\<lambda> x. P(x) \<longleftrightarrow> Q(x))" by linarith
qed

lemma ex_definable_lemma1: 
  "A = {C, D} \<longleftrightarrow> (\<forall>u::Set. u \<in> A \<longleftrightarrow> u = C \<or> u = D)"
using Ex4_4 Rep_Set_inject pairing by auto 

lemma ex_definable_lemma2:
  "A = {{C}, {D,E}} \<longleftrightarrow> 
  (\<forall>u::Set. u \<in> A \<longleftrightarrow> ((\<forall> v::Set. v \<in> u \<longleftrightarrow> v = C) \<or> (\<forall> v::Set. v \<in> u \<longleftrightarrow> v = D \<or> v = E)))" 
proof -
  have "A = {{C}, {D,E}} \<longleftrightarrow> (\<forall>u::Set. u \<in> A \<longleftrightarrow> u = {C} \<or> u = {D,E})" 
    by (rule ex_definable_lemma1)
  also have "\<dots> \<longleftrightarrow>  (\<forall>u::Set. u \<in> A \<longleftrightarrow> ((\<forall> v::Set. v \<in> u \<longleftrightarrow> v = C) \<or> u = {D,E}))"
    using ex_definable_lemma1 by auto
  also have "\<dots> \<longleftrightarrow>  (\<forall>u::Set. u \<in> A \<longleftrightarrow> 
    ((\<forall> v::Set. v \<in> u \<longleftrightarrow> v = C) \<or> (\<forall> v::Set. v \<in> u \<longleftrightarrow> v = D \<or> v = E)))" 
    using ex_definable_lemma1 by auto
  finally show ?thesis by auto
qed

lemma ex_definable[defining]:
assumes "definable P"
shows "definable (\<lambda> x. \<exists> y::Set. P(\<langle>x,y\<rangle>))"
proof -
  obtain p where p_def: "\<forall>i. FOL_True p i \<longleftrightarrow> P(i(0))" using assms definable_def by auto
  def "n" == "(FOL_MaxVar p)::nat"
  {fix i :: "nat \<Rightarrow> Set"
  have "(\<exists> y::Set. P(\<langle>i(0), y\<rangle>)) \<longleftrightarrow> (\<exists> A::Set. \<exists> y::Set. A = \<langle>i(0), y\<rangle> \<and> P(A))" by auto
  also have "\<dots> \<longleftrightarrow> (\<exists> A::Set. \<exists> y::Set. A = {{i(0)}, {i(0),y}} \<and> P(A))" 
    using ordered_pair_def by auto
  also have 
  "\<dots> \<longleftrightarrow> (\<exists> A::Set. \<exists> y::Set. 
      (\<forall>u::Set. u \<in> A \<longleftrightarrow> ((\<forall> v::Set. v \<in> u \<longleftrightarrow> v = i(0)) \<or> 
                            (\<forall> v::Set. v \<in> u \<longleftrightarrow> v = i(0) \<or> v = y))) 
      \<and> P(A))" 
    using ex_definable_lemma2 by auto
  also have "\<dots> \<longleftrightarrow> 
    (FOL_True (FEx (n+4) (FAnd (FEx (n+3)
                                 (FAll (n+2) 
                                    (FIff (FBelongs (FVar (n+2)) 
                                                    (FVar  (n+4))) 
                                          (FOr (FAll (n+1) 
                                                     (FIff (FBelongs (FVar (n+1)) 
                                                                     (FVar (n+2)))
                                                           (FEquals (FVar (n+1)) 
                                                                    (FVar 0))))
                                               (FAll (n+1) 
                                                     (FIff (FBelongs (FVar (n+1)) 
                                                                     (FVar (n+2)))
                                                           (FOr (FEquals (FVar (n+1)) 
                                                                         (FVar 0))
                                                                (FEquals (FVar (n+1)) 
                                                                         (FVar (n+3))))))))))
                         (single_subst_f p 0 (n+4)))) i)" 
    by (simp add: Update_def single_subst_lemma n_def FOL_MaxVar_Dom p_def Rep_Set_inject)
  finally have "(\<exists> y. P(\<langle>i(0), y\<rangle>)) \<longleftrightarrow> 
   (FOL_True (FEx (n+4)
                   (FAnd (FEx (n+3)
                              (FAll (n+2) 
                                    (FIff (FBelongs (FVar (n+2)) 
                                                    (FVar  (n+4))) 
                                          (FOr (FAll (n+1) 
                                                     (FIff (FBelongs (FVar (n+1)) 
                                                                     (FVar (n+2)))
                                                           (FEquals (FVar (n+1)) 
                                                                    (FVar 0))))
                                               (FAll (n+1) 
                                                     (FIff (FBelongs (FVar (n+1)) 
                                                                     (FVar (n+2)))
                                                           (FOr (FEquals (FVar (n+1)) 
                                                                         (FVar 0))
                                                                (FEquals (FVar (n+1)) 
                                                                         (FVar (n+3))))))))))
                         (single_subst_f p 0 (n+4)))) i)" by simp }
  then have "\<forall> i. (\<exists> y. P(\<langle>i(0), y\<rangle>)) \<longleftrightarrow> 
    (FOL_True (FEx (n+4) 
                   (FAnd (FEx (n+3)
                              (FAll (n+2) 
                                    (FIff (FBelongs (FVar (n+2)) 
                                                    (FVar (n+4)))   
                                          (FOr (FAll (n+1) 
                                                     (FIff (FBelongs (FVar (n+1)) 
                                                                     (FVar (n+2)))
                                                           (FEquals (FVar (n+1)) 
                                                                    (FVar 0))))
                                               (FAll (n+1) 
                                                     (FIff (FBelongs (FVar (n+1)) 
                                                                     (FVar (n+2)))
                                                           (FOr (FEquals (FVar (n+1)) 
                                                                         (FVar 0))
                                                                (FEquals (FVar (n+1)) 
                                                                         (FVar (n+3))))))))))
                         (single_subst_f p 0 (n+4)))) i)" by auto
  then show "definable (\<lambda> x. (\<exists> y. P(\<langle>x, y\<rangle>)))" unfolding definable_def by blast
qed

lemma all_definable[defining]:
assumes "definable P"
shows "definable (\<lambda> x. \<forall> y. P(\<langle>x,y\<rangle>))"
proof -
  from assms have "definable (\<lambda>x. \<not> (P x))" by (simp add: defining)
  then have "definable (\<lambda>x. \<exists>y. \<not> (P \<langle>x,y\<rangle>))" by (rule ex_definable)
  then have "definable (\<lambda>x. \<not> (\<exists>y. \<not> (P \<langle>x,y\<rangle>)))" by (rule not_definable)
  then show "definable (\<lambda> x. \<forall> y. P(\<langle>x,y\<rangle>))" by auto
qed

lemma belongs_definable_lemma[defining]:
shows "definable (\<lambda> x. x \<in> C)"
unfolding definable_def
proof 
  def "D" == "FBelongs (FVar 0) (FConst C)"
  show " (\<forall> i. FOL_True D i \<longleftrightarrow> (i(0)) \<in> C)" unfolding D_def by auto 
qed


lemma singleton_definable[defining]:
shows "\<forall>C::Set. definable (\<lambda> x. x = C)"
unfolding definable_def
proof  
  fix C
  show "\<exists>\<phi>. \<forall>i. FOL_True \<phi> i = (i 0 = C)"
  proof
    show "\<forall> i. FOL_True (FEquals (FVar 0) (FConst C)) i = (i 0 = C)" by (simp add: Rep_Set_inject) 
  qed
qed


text{* We will often need the FOL_Formula which describes that a set variable is 
       the ordered pair of two other set varianles, so we separate it below: *}

definition Pair\<phi> :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> FOL_Formula"
--"\<open>x\<^sub>l = \<langle>x\<^sub>m, x\<^sub>n\<rangle>\<close>"
where "Pair\<phi> l m n = (FAll 99 
                         (FIff (FBelongs (FVar 99) (FVar l))
                               (FOr (FAll 999 
                                      (FIff (FBelongs (FVar 999) (FVar 99)) 
                                            (FEquals (FVar 999) (FVar m))))
                                    (FAll 999 
                                      (FIff (FBelongs (FVar 999) (FVar 99))   
                                            (FOr (FEquals (FVar 999) (FVar m))
                                                 (FEquals (FVar 999) (FVar n))))))))"

lemma cartesian_definable [defining]:
shows "definable (\<lambda> x. \<exists> u v. x = \<langle>u, v\<rangle>)" unfolding definable_def
proof -
  let ?f = "\<lambda> x. \<exists> u v. x = \<langle>u, v\<rangle>"
  let ?\<phi> = "(FEx 10 (FEx 20 (Pair\<phi> 0 10 20)))"
  have "\<forall>i. (FOL_True ?\<phi> i = (?f (i 0)))" by (simp add: ordered_pair_def Update_def Rep_Set_inject 
    FOL_MaxVar_Dom Pair\<phi>_def ex_definable_lemma2)
  thus "\<exists>\<phi>. \<forall>i. FOL_True \<phi> i = (\<exists>u v. i 0 = \<langle>u, v\<rangle>) " ..
qed

lemma belongs_definable[defining]:
shows "definable (\<lambda> x. \<exists> u v ::Set. x = \<langle>u, v\<rangle> \<and> u \<in> v)" unfolding definable_def
proof -
 let ?f = "\<lambda> x. \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> v"
 let ?\<phi> = "(FEx 10 (FEx 20 (FAnd (Pair\<phi> 0 10 20)
                                 (FBelongs (FVar 10) (FVar 20)))))"
 have "\<forall>i. FOL_True ?\<phi> i = (?f (i 0))" by (simp add: ordered_pair_def Update_def Rep_Set_inject 
   FOL_MaxVar_Dom Pair\<phi>_def ex_definable_lemma2)
 thus "\<exists>\<phi>. \<forall>i. FOL_True \<phi> i = ?f(i(0))" ..
qed

lemma equals_definable[defining]:
shows "definable (\<lambda> x. \<exists> u. x = \<langle>u,u\<rangle>)" unfolding definable_def
proof -
  let ?f = "\<lambda> x. \<exists> u. x = \<langle>u, u\<rangle>"
  let ?\<phi> = "(FEx 10 (Pair\<phi> 0 10 10))"
  have "\<forall>i. FOL_True ?\<phi> i = (?f (i 0))" by (simp add: ordered_pair_def Update_def
     Rep_Set_inject FOL_MaxVar_Dom Pair\<phi>_def ex_definable_lemma2)
  thus "\<exists>\<phi>. \<forall>i. FOL_True \<phi> i = (?f(i(0)))" ..
qed

(* class comprehension lemmata *)

lemma comprehensionE:
assumes "u \<in> {x \<bar> P(x)}" 
shows "(P u)"
by (simp add: assms class_comprehensionE(2))

lemma comprehensionI:
assumes "definable P" and "P u"
shows "u \<in> {x \<bar> P(x)}" 
using class_comprehensionI
by (simp add: assms(1) assms(2)) 

lemma comprehension_true_is_universe:  "{x\<bar> True} = \<V>"
by (simp add: set_extensionality Ex4_9_b class_comprehension_property true_definable)

lemma comprehension_false_is_empty: "{x\<bar> False} = \<emptyset>"
using empty_set class_comprehensionE(2) set_extensionality by auto

lemma comprehension_not_is_Co_comprehension: 
assumes "definable P"
shows "{x\<bar> \<not>P(x)} = Co({x\<bar> P(x)}) "
proof-
{ fix x :: Set
    from assms have "definable (\<lambda>x. \<not> P (x))" by (simp add: defining)
    then have "x \<in> {x\<bar> \<not>P(x)} \<longleftrightarrow> \<not> P x" using class_comprehension_property by blast 
    also have "\<dots> \<longleftrightarrow> x \<notin> {x\<bar> P(x)}" by (simp add: assms class_comprehension_property) 
    also have "... \<longleftrightarrow> x \<in> Co({x\<bar> P(x)})" by (simp add: B3) 
    finally have "x \<in> {x\<bar> \<not>P(x)} \<longleftrightarrow>  x \<in> Co({x\<bar> P(x)})" by auto
  }
  then show ?thesis by (simp add: set_extensionality)
qed

lemma comprehension_belongs: "{x\<bar> x \<in> A} = A"
proof -
  have "\<forall> u. u \<in> {x\<bar> x \<in> A} \<longleftrightarrow> u \<in> A"
    by (metis CollectI Rep_Set_cases belongs_definable_lemma class_comprehension_property 
    set_predicate_def universe) 
  then show ?thesis by (auto simp add: set_extensionality)
qed


lemma comprehension_conj_is_intersection: 
assumes "definable P" "definable Q"
shows "{x\<bar> P(x) \<and> Q(x)} = {x\<bar> P(x)} \<inter> {x\<bar> Q(x)}"
proof -
 {fix x :: Set
   from assms have "definable (\<lambda> x. P(x) \<and> Q(x))" by (simp add: defining)
   then have "x \<in> {x\<bar> P(x) \<and> Q(x)} \<longleftrightarrow> P(x) \<and> Q(x)" by (simp add: class_comprehension_property) 
   also have "\<dots> \<longleftrightarrow> x \<in> {x\<bar> P(x)} \<and> x \<in> {x\<bar> Q(x)}" 
    by (simp add: assms(1) assms(2) class_comprehension_property)
   also have "\<dots> \<longleftrightarrow>  x \<in> {x\<bar> P(x)} \<inter> {x\<bar> Q(x)}" by (simp add: B2) 
   finally have "x \<in> {x\<bar> P(x) \<and> Q(x)} \<longleftrightarrow> x \<in> {x\<bar> P(x)} \<inter> {x\<bar> Q(x)}" by auto }
 then show ?thesis by (simp add: set_extensionality)
qed 

lemma comprehension_disj_is_union: 
assumes "definable P" "definable Q"
shows "{x\<bar> P(x) \<or> Q(x)} = {x\<bar> P(x)} \<union> {x\<bar> Q(x)}"
proof -
 {fix x :: Set
   from assms have "definable (\<lambda> x. P(x) \<or> Q(x))" by (simp add: defining)
   then have "x \<in> {x\<bar> P(x) \<or> Q(x)} \<longleftrightarrow> P(x) \<or> Q(x)" by (simp add: class_comprehension_property) 
   also have "\<dots> \<longleftrightarrow> x \<in> {x\<bar> P(x)} \<or> x \<in> {x\<bar> Q(x)}" 
    by (simp add: assms(1) assms(2) class_comprehension_property)
   also have "\<dots> \<longleftrightarrow>  x \<in> {x\<bar> P(x)} \<union> {x\<bar> Q(x)}" by (simp add: Ex4_9_a) 
   finally have "x \<in> {x\<bar> P(x) \<or> Q(x)} \<longleftrightarrow> x \<in> {x\<bar> P(x)} \<union> {x\<bar> Q(x)}" by auto }
 then show ?thesis by (simp add: set_extensionality)
qed 


end