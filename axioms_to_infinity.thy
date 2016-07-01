(* Section "An Axiom System", right after the class existence theorem. *)

theory axioms_to_infinity
imports class_comprehension auxiliary1
begin

(* page 233, after the proof of the class existence theorem. *)

text{* A definition of the form $x \in X \leftrightarrow \phi(x)$ is done with a proof
       of its definability ("[name]_definable[defining]:"), then an Isabelle definition of a 
       metafunction symbol ("[name]") defined using the class  { | }, and then a 
       lemma that contains the actual ZF-definition. *}
       
(* The following is Example 1. *) 

lemma cartesian_product_definable[defining]: 
shows "definable (\<lambda> x::Set. \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B)"
unfolding definable_def 
proof -
  let ?f = "\<lambda> x::Set. \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B"
  let ?\<phi> = "(FEx 10 (FEx 20                                  (* x\<^sub>1\<^sub>0 for u,  x\<^sub>2\<^sub>0 for v    *)
                (FAnd (FAnd  
                        (Pair\<phi> 0 10 20)
                        (FBelongs (FVar 10) (FConst A)))
                      (FBelongs (FVar 20) (FConst B)))))"
  have "\<forall>i. FOL_True ?\<phi> i = (?f (i 0))" by (simp add: ordered_pair_def Update_def
     Rep_Set_inject FOL_MaxVar_Dom Pair\<phi>_def ex_definable_lemma2)
  thus "\<exists>\<phi>. \<forall>i. FOL_True \<phi> i = (?f(i(0)))" by blast
qed

definition
  cartesian_product :: "Class \<Rightarrow> Class \<Rightarrow> Class" (infixl "\<times>" 79)
where
  "A \<times> B = {x \<bar> \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B }"

lemma cartesian_product_lemma:
  "\<forall>x. x \<in> (A \<times> B) \<longleftrightarrow> (\<exists>u v. x = \<langle>u,v\<rangle> \<and> u \<in> A \<and> v \<in> B)"
proof
  fix x A B
  from cartesian_product_definable 
    have eq: "\<forall>x::Set. x \<in> {x \<bar> \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B }
            \<longleftrightarrow>  (\<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B)"
    using class_comprehension_property by simp
  show "x \<in> (A \<times> B) \<longleftrightarrow> (\<exists>u v. x = \<langle>u,v\<rangle> \<and> u \<in> A \<and> v \<in> B)" 
  proof
    assume assm: "x \<in> A \<times> B"
    then have "set(x)" using set_predicate_def by auto
    from assm cartesian_product_def have **: "x \<in> {x \<bar> \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B }"
      by simp
    from eq `set(x)` have "x \<in> {x \<bar> \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B }
            \<longleftrightarrow>  (\<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B)" 
      by (metis Abs_Set_inverse assm cartesian_product_def mem_Collect_eq universe) 
    with ** show "(\<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B)" by simp
    next
    assume assm: "(\<exists>u v. x = \<langle>u,v\<rangle> \<and> u \<in> A \<and> v \<in> B)"
    then have "set(x)" using Ex4_9_b universe by blast
    from eq `set(x)` have "x \<in> {x \<bar> \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v \<in> B }"
      by (metis assm cartesian_product_def) 
    with cartesian_product_def show "x \<in> A \<times> B" by simp
  qed
qed

(* abbreviation square :: "Class \<Rightarrow> Class" ("((_)/\<^sup>2)" 90)
  where "Y\<^sup>2 \<equiv> (Y \<times> Y)" *)     (* square is included below, and this becomes a lemma *)

fun n_product :: "Class \<Rightarrow> nat \<Rightarrow> Class" ("(1_)/\<^bsup>(2_)/\<^esup>" 80)
  where "Y\<^bsup>0\<^esup> = \<emptyset>" | "Y\<^bsup>(Suc 0)\<^esup> = Y" | "Y\<^bsup>(Suc (Suc n))\<^esup> = (Y\<^bsup>(Suc n)\<^esup>)\<times>Y"
notation n_product ("(1_)/\<^sup>_" 80)

lemma square: "Y\<^sup>2 \<equiv> (Y \<times> Y)" by (simp add: numeral_2_eq_2) 

definition relation_predicate :: "Class \<Rightarrow> bool" ("Rel")
  where "Rel(X) \<longleftrightarrow> X \<subseteq> (\<V>\<^sup>2) "
notation relation_predicate ("(_ is a relation)" 70)

text{* \textbf{FOMUS workshop exercise:} *}

lemma n_product_remark1: "(\<V>\<^sup>2) = { x \<bar> \<exists>u v::Set. x=\<langle>u,v\<rangle> }"
sorry

text{* \textbf{FOMUS workshop extra exercise:} *}

lemma n_product_remark2: "(\<V>\<^sup>n) = { x \<bar> \<exists>i::(nat\<Rightarrow>Set). x = \<langle>\<dots>, i(n)\<rangle> }"
sorry

(* page 234 *)

text{* A definition of the form $x \in X \leftrightarrow \phi(x)$ is done with:
       \begin{enumerate}
       \item a proof that the metafunction \tt{$\lambda x. \phi(x)$} is definable,
       \item the class definition using the \tt{$\{ x \bar \phi(x)\}$} notation, and 
       \item a lemma that contains the actual ZF definition using \tt{$x\in X \longleftrightarrow 
             \phi(x)$}. 
       \end{enumerate}
The first and the last lemma should be the given as \tt{name_definable[defining]} and 
\tt{name_lemma}, where \tt{name} is the name of the class defined in step 2. Just as below:
*}

(* Consider extracting formula for subset: Subset\<phi> *)

lemma power_class_definable[defining]: 
  shows "definable (\<lambda> x. x \<subseteq> Y)"
proof -
  def "f" == "(\<lambda> x. x \<subseteq> Y)"
  def "\<phi>" == "(FAll 10 (FImp (FBelongs (FVar 10) (FVar 0)) 
                             (FBelongs (FVar 10) (FConst Y))))"
  {
   fix i
   have "FOL_True \<phi> i = (f (i 0))" 
   by ( simp add: f_def ordered_pair_def Update_def
     Rep_Set_inject FOL_MaxVar_Dom \<phi>_def subset)
  }
  then show ?thesis unfolding definable_def f_def by auto
qed


definition 
  power_class :: "Class \<Rightarrow> Class" ("\<P>")
  where "\<P>(Y) = {x \<bar> x \<subseteq> Y}"


lemma power_class_lemma: "\<forall>x::Set. (x \<in> \<P>(Y)) \<longleftrightarrow> (x \<subseteq> Y)"
using power_class_def comprehensionE comprehensionI power_class_definable by auto


lemma sum_class_definable: "definable (\<lambda> x. \<exists>v::Set. x \<in> v \<and> v \<in> X)"
proof -
  def "f" == "(\<lambda> x. \<exists>v::Set. x \<in> v \<and> v \<in> X)"
  def "\<phi>" == "(FEx 10 (FAnd  (FBelongs (FVar 0) (FVar 10)) 
                             (FBelongs (FVar 10) (FConst X))))"
  {
   fix i
   have "FOL_True \<phi> i = (f (i 0))" 
   by ( simp add: f_def ordered_pair_def Update_def
     Rep_Set_inject FOL_MaxVar_Dom \<phi>_def)
  }
  then show ?thesis unfolding definable_def f_def by auto
qed

definition
  sum_class :: "Class \<Rightarrow> Class" ("\<Union>")
  where "\<Union>X = {x \<bar> \<exists>v::Set. x \<in> v \<and> v \<in> X }"

lemma sum_class_lemma: "\<forall>x::Set. x \<in> \<Union>X \<longleftrightarrow> (\<exists>v::Set. x \<in> v \<and> v \<in> X)"
by (simp add: class_comprehension_property sum_class_def sum_class_definable)

lemma identity_relation_definable: "definable (\<lambda> x. \<exists>u. x = \<langle>u,u\<rangle>)" 
using equals_definable .

definition 
  identity_relation :: "Class" ("\<I>")
  where "\<I> = {x \<bar> \<exists>u. x = \<langle>u,u\<rangle>}"

lemma identity_relation_lemma: "\<forall>x::Set. x \<in> \<I> \<longleftrightarrow> (\<exists>u::Set. x = \<langle>u,u\<rangle>)"
by (simp add: class_comprehension_property identity_relation_def identity_relation_definable)


text{* \textbf{FOMUS workshop extra exercise:} *}

lemma Cor4_5: --"Corollary to the class existence theorem."
    fixes n m ::nat
    fixes \<phi> :: FOL_Formula
  assumes "n+m \<le> (FOL_MaxVar \<phi>)"
    shows "\<exists>! W::Class. W \<subseteq> (\<V>\<^sup>n) \<and> (\<forall>i::nat\<Rightarrow>Set. (\<langle>\<dots>,i(n)\<rangle> \<in> W \<longleftrightarrow> (FOL_True \<phi> i)))" 
sorry 

(* TO DO: Add notation to define classes of tuples by {\<langle>x\<^sub>0, \<dots>, x\<^sub>n\<rangle> \<bar> \<phi>\<langle>x\<^sub>0, \<dots>, x\<^sub>n\<rangle>} *)

(* page 235 *)

(* The following is Example 1 *)

lemma inverse_relation_definable[defining]: 
  shows "definable (\<lambda> x::Set. \<exists>u v. x = \<langle>u,v\<rangle> \<and> \<langle>v,u\<rangle> \<in> X)"
unfolding definable_def
proof -
  (* Idea \<langle>v, u\<rangle> \<in> X \<longleftrightarrow> \<exists> z. z = \<langle>v, u\<rangle> \<and> z \<in> X*)
  let ?f = "\<lambda> x::Set. \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> \<langle>v, u\<rangle> \<in> X"
  let ?g = "\<lambda> x::Set. \<exists> u v :: Set. x = \<langle>u, v\<rangle> \<and> (\<exists> z :: Set. z = \<langle>v, u\<rangle> \<and> z \<in> X)"
  have "?f = ?g"  by auto
  let ?\<phi> = "(FEx 10 (FEx 20 
                      (FAnd  (Pair\<phi> 0 10 20) 
                             (FEx 50 (FAnd (Pair\<phi> 50 20 10)
                                           (FBelongs (FVar 50) (FConst X)))))))"
  have "\<forall>i. FOL_True ?\<phi> i = (?g (i 0))" by (simp add: ordered_pair_def Update_def
     Rep_Set_inject FOL_MaxVar_Dom Pair\<phi>_def ex_definable_lemma2)
  then have "\<forall>i. FOL_True ?\<phi> i = (?f (i 0))" unfolding \<open>?f = ?g\<close> by auto
  then show "\<exists>\<phi>. \<forall>i. FOL_True \<phi> i = (?f (i 0))"  by blast
qed

definition 
  inverse_relation :: "Class \<Rightarrow> Class" ("Inv")
  where "Inv(X) = {z \<bar> \<exists>u v. z = \<langle>u,v\<rangle> \<and> \<langle>v,u\<rangle> \<in> X }"

lemma inverse_relation_lemma: "\<langle>x,y\<rangle> \<in> Inv(X) \<longleftrightarrow> \<langle>y,x\<rangle> \<in> X" 
proof
  assume "\<langle>x,y\<rangle> \<in> Inv(X)"
  with inverse_relation_def have "\<langle>x,y\<rangle> \<in> { z \<bar> \<exists>u v. z = \<langle>u,v\<rangle> \<and> \<langle>v,u\<rangle> \<in> X }" by simp
  with comprehensionE have "\<exists>u v. \<langle>x,y\<rangle> = \<langle>u,v\<rangle> \<and> \<langle>v,u\<rangle> \<in> X" by auto
  then show "\<langle>y,x\<rangle> \<in> X" using Prop4_3 by blast
  next
  fix y x
  assume "\<langle>y,x\<rangle> \<in> X"
  then have "\<exists>u v. \<langle>x,y\<rangle> = \<langle>u,v\<rangle> \<and> \<langle>v,u\<rangle> \<in> X" by auto 
  with comprehensionI inverse_relation_definable inverse_relation_def show "\<langle>x,y\<rangle> \<in> Inv(X)" 
    by simp
qed

lemma range_definable[defining]:
  shows "definable (\<lambda>x::Set . \<exists>v.\<langle>v,x\<rangle> \<in> Y)"
proof -
  (* Idea \<exists> v. \<langle>v, x\<rangle> \<in> X \<longleftrightarrow> \<exists> v z. z = \<langle>v, x\<rangle> \<and> z \<in> X*)
  let ?f = "\<lambda> x::Set. \<exists> v :: Set. \<langle>v, x\<rangle> \<in> Y"
  let ?g = "\<lambda> x::Set. \<exists>v :: Set. \<exists>z :: Set. z = \<langle>v,x\<rangle> \<and> z \<in> Y"
  have "?f = ?g" by auto
  let ?\<phi> = "(FEx 10 (* v *)
             (FEx 20 (* z *)
               (FAnd  (Pair\<phi> 20 10 0)
                      (FBelongs (FVar 20) (FConst Y)))))" 
  have "\<forall>i. FOL_True ?\<phi> i = (?g (i 0))" by (simp add: ordered_pair_def Update_def Rep_Set_inject 
    FOL_MaxVar_Dom Pair\<phi>_def ex_definable_lemma2)
  then have "\<forall>i. FOL_True ?\<phi> i = (?f (i 0))" unfolding \<open>?f = ?g\<close> by auto
  thus ?thesis unfolding definable_def by blast
qed

definition
  range :: "Class \<Rightarrow> Class" ("ran")
  where "ran(Y) = {x \<bar> \<exists>v. \<langle>v,x\<rangle> \<in> Y}"

lemma range_lemma: "\<forall>u::Set. (u \<in> ran(Y)) \<longleftrightarrow> (\<exists>v::Set.\<langle>v,u\<rangle> \<in> Y)"
by (simp add: class_comprehension_property range_def range_definable)

lemma Ex4_12_a: "\<Union>\<emptyset> = \<emptyset>"
proof (unfold set_extensionality)
  show "\<forall>x::Set. x \<in> \<Union> (\<emptyset>) \<longleftrightarrow> x \<in> \<emptyset>"
  proof
    fix x::Set
    have "x \<in> \<Union> (\<emptyset>) \<longleftrightarrow> (\<exists>v::Set. x \<in> v \<and> v \<in> \<emptyset>)" using sum_class_lemma by simp
    then show "x \<in> \<Union> (\<emptyset>) \<longleftrightarrow> x \<in> \<emptyset>" by (simp add:empty_set)
  qed
qed

lemma Ex4_12_b: "\<Union>{\<emptyset>} = \<emptyset>"
proof (unfold set_extensionality)
  show "\<forall>x::Set. x \<in> \<Union>{\<emptyset>} \<longleftrightarrow> x \<in> \<emptyset>"
  proof
    fix x::Set
    have "x \<in> \<Union>{\<emptyset>} \<longleftrightarrow> (\<exists>v::Set. x \<in> v \<and> v \<in> {\<emptyset>})" using sum_class_lemma by simp
    then show "x \<in> \<Union>{\<emptyset>} \<longleftrightarrow> x \<in> \<emptyset>" using empty_set sum_class_def using pairing by auto 
  qed
qed

lemma Ex4_12_c: "\<Union>\<V> = \<V>"
using Ex4_9_b Prop4_1_a subset singletonE sum_class_lemma ex_definable_lemma1 by blast

lemma Ex4_12_d: "\<P>(\<V>) = \<V>"
by (meson Ex4_10_c Ex4_10_k Prop4_1_a power_class_lemma subset)

lemma Ex4_12_e: "X \<subseteq> Y \<longrightarrow> (\<Union>X \<subseteq> \<Union>Y \<and> \<P>(X) \<subseteq> \<P>(Y))"
using subset sum_class_lemma by (meson power_class_lemma subset subclass'_def)

lemma Ex4_12_f: "\<Union>(\<P>(X)) = X"
proof (unfold set_extensionality)
  show "\<forall>x::Set. x \<in> \<Union> (\<P> X) \<longleftrightarrow> x \<in> X"
  proof
    fix x::Set
    have "x\<in>\<Union> (\<P> X) \<longleftrightarrow> (\<exists>v::Set. x \<in> v \<and> (v \<subseteq> X))" using sum_class_lemma power_class_lemma 
      by simp
    then have "x\<in>\<Union> (\<P> X) \<longleftrightarrow> (x \<in> {x} \<and> ({x} \<subseteq> X))" by (metis pairing subclass'_def) 
    then show "x \<in> \<Union> (\<P> X) \<longleftrightarrow> x \<in> X" by (metis pairing subset) 
  qed
qed

lemma Ex4_12_g: "X \<subseteq> \<P>(\<Union>X)"
by (meson power_class_lemma subset sum_class_lemma)

lemma Ex4_12_h: "(X \<inter> Y) \<times> (W \<inter> Z) = (X \<times> W) \<inter> (Y \<times> Z)"
proof (rule equalityI)
  show "X \<inter> Y \<times> W \<inter> Z \<subseteq> (X \<times> W) \<inter> (Y \<times> Z)"
  proof (rule subsetI)
    fix x
    assume "x \<in> X \<inter> Y \<times> W \<inter> Z "
    then show "x \<in> (X \<times> W) \<inter> (Y \<times> Z)"
      using B2 cartesian_product_lemma by fastforce
  qed
  show "(X \<times> W) \<inter> (Y \<times> Z) \<subseteq> X \<inter> Y \<times> W \<inter> Z"
  proof (rule subsetI)
    fix x 
    assume assm: "x \<in> (X \<times> W) \<inter> (Y \<times> Z)"
    then have "x \<in> X \<times> W" using notin_inter_mono by auto
    from this obtain y z where "x = \<langle>y, z\<rangle>" using cartesian_product_lemma by blast
    with \<open>x \<in> X \<times> W\<close> have "y \<in> X" by (metis B5 cartesian_product_lemma) 
    from \<open>x \<in> X \<times> W\<close> \<open>x = \<langle>y, z\<rangle>\<close> have "z \<in> W" 
      by (metis Prop4_3 Rep_Set_inject cartesian_product_lemma) 
    from assm have "x \<in> Y \<times> Z" using B2 \<open>x \<in> X \<times> W\<close> cartesian_product_lemma by fastforce
    with \<open>x = \<langle>y, z\<rangle>\<close> have "y \<in> Y" by (metis B5 cartesian_product_lemma) 
    from \<open>x \<in> Y \<times> Z\<close> \<open>x = \<langle>y,z\<rangle>\<close> have "z \<in> Z" 
      by (metis Prop4_3 Rep_Set_inverse cartesian_product_lemma) 
    from \<open>y \<in> Y\<close> \<open>y \<in> X\<close> have "y \<in> X \<inter> Y" using B2 by simp
    from \<open>z \<in> W\<close> \<open>z \<in> Z\<close> have "z \<in> W \<inter> Z" using B2 by simp
    with \<open>y \<in> X \<inter> Y\<close> \<open>x = \<langle>y,z\<rangle>\<close> show "x \<in> X \<inter> Y \<times> W \<inter> Z"
      using cartesian_product_lemma by auto
  qed
qed

lemma Ex4_12_i: "(X \<union> Y) \<times> (W \<union> Z) = (X \<times> W) \<union> (X \<times> Z) \<union> (Y \<times> W) \<union> (Y \<times> Z)"
proof (rule equalityI)
  show "X \<union> Y \<times> W \<union> Z \<subseteq> (X \<times> W) \<union> (X \<times> Z) \<union> (Y \<times> W) \<union> (Y \<times> Z)" 
  proof (rule subsetI)
    fix x
    assume assm: "x \<in> X \<union> Y \<times> W \<union> Z"
    then obtain y z where xyz: "x = \<langle>y, z\<rangle>" using cartesian_product_lemma by blast
    with assm have "y \<in> X \<union> Y" by (metis Prop4_3 Rep_Set_inverse cartesian_product_lemma) 
    then have "y \<in> X \<or> y \<in> Y" by (simp add: Ex4_9_a)
    from assm xyz have "z \<in> W \<union> Z" by (metis Prop4_3 Rep_Set_inverse cartesian_product_lemma) 
    then have "z \<in> W \<or> z \<in> Z" by (simp add: Ex4_9_a)
    show "x \<in> (X \<times> W) \<union> (X \<times> Z) \<union> (Y \<times> W) \<union> (Y \<times> Z)" 
    proof (cases "y \<in> X")
      assume "y \<in> X"
      then have "x \<in> (X \<times> W) \<union> (X \<times> Z)" 
        using \<open>z \<in> W \<or> z \<in> Z\<close> cartesian_product_lemma union_iff_or xyz by blast
      then show ?thesis by (simp add: B2 B3 xyz)
      next
      assume "y \<notin> X"
      then have "y \<in> Y" using \<open>y \<in> X \<or>  y \<in> Y\<close> by blast
      then have "x \<in> (Y \<times> W) \<union> (Y \<times> Z)" 
        using \<open>z \<in> W \<or> z \<in> Z\<close> cartesian_product_lemma union_iff_or xyz by blast      
      then show ?thesis by (simp add: B2 B3 xyz)
    qed
  qed

  show "(X \<times> W) \<union> (X \<times> Z) \<union> (Y \<times> W) \<union> (Y \<times> Z) \<subseteq> X \<union> Y \<times> W \<union> Z"
  proof (rule subsetI)
    fix x
    assume assm: "x \<in> (X \<times> W) \<union> (X \<times> Z) \<union> (Y \<times> W) \<union> (Y \<times> Z)"
    then obtain y z where "x = \<langle>y,z\<rangle>"
      using cartesian_product_lemma union_iff_or by auto
    from assm have "x \<in> X \<times> W \<or> x \<in> X \<times> Z \<or> x \<in> Y \<times> W \<or> x \<in> Y \<times> Z"
      by (simp add: union_iff_or)
    thus "x \<in> (X \<union> Y) \<times> (W \<union> Z)" using cartesian_product_lemma union_iff_or Ex4_9_c assm
      by fastforce
  qed
qed

lemma Ex4_12_j: "\<P>(X \<inter> Y) = (\<P>(X)) \<inter> \<P>(Y)"
proof (rule equalityI)
  show "\<P>(X \<inter> Y) \<subseteq> (\<P>(X)) \<inter> \<P>(Y)"
  proof (rule subsetI)
    fix x::Set
    assume assm: "x \<in> \<P>(X \<inter> Y)"
    then have "x \<subseteq> X \<inter> Y" using power_class_lemma by simp
    then have "x \<subseteq> X" using B2 subset by blast
    then have 1: "x \<in> \<P>(X)" using power_class_lemma by simp
    from \<open>x \<subseteq> X \<inter> Y\<close> have "x \<subseteq> Y" using B2 subset by blast
    then have 2: "x \<in> \<P>(Y)" using power_class_lemma by simp
    from 1 2 show "x \<in> (\<P>(X)) \<inter> \<P>(Y)" using B2 by simp
  qed
  
  show "(\<P>(X)) \<inter> \<P>(Y) \<subseteq> \<P>(X \<inter> Y)"
  proof (rule subsetI)
    fix x::Set
    assume assm: "x \<in> (\<P>(X)) \<inter> \<P>(Y)"
    then have "x \<in> \<P>(X)" using B2 by simp
    then have "x \<subseteq> X" using power_class_lemma by simp
    from assm have "x \<in> \<P>(Y)" using B2 by simp
    then have "x \<subseteq> Y" using power_class_lemma by simp
    with \<open>x \<subseteq> X\<close> have "x \<subseteq> X \<inter> Y" using Ex4_10_c Ex4_10_e by metis
    then show "x \<in> \<P>(X \<inter> Y)" using power_class_lemma by simp
  qed
qed

lemma Ex4_12_k: "(\<P>(X)) \<union> \<P>(Y) \<subseteq> \<P>(X \<union> Y)"
proof (rule subsetI)
  fix x::Set
  assume "x \<in> (\<P>(X)) \<union> \<P>(Y)"
  then have "x \<in> \<P>(X) \<or> x \<in> \<P>(Y)" by (simp add: Ex4_9_a)
  then have "x \<subseteq> X \<or> x \<subseteq> Y" using power_class_lemma by simp
  then have "x \<subseteq> X \<union> Y" by (smt Ex4_10_a Ex4_10_d Ex4_10_f)
  then show "x \<in> \<P>(X \<union> Y)" using power_class_lemma by simp
qed


lemma Ex4_12_m: "\<Union>(X\<union>Y) = (\<Union>X) \<union> (\<Union>Y)"
proof (rule equalityI)
  show " \<Union> (X \<union> Y) \<subseteq> \<Union> X \<union> \<Union> Y" 
  proof (rule subsetI)
    fix x::Set
    assume "x \<in> \<Union>(X \<union> Y)"
    then obtain z::Set where *: "z \<in> X \<union> Y \<and> x \<in> z" using sum_class_lemma by metis
    then have "z \<in> X \<or> z \<in> Y" by (simp add: union_iff_or)
    with * have "x \<in> \<Union>X \<or> x \<in> \<Union>Y" using sum_class_lemma by blast
    then show "x \<in> \<Union> X \<union> \<Union> Y" using union_iff_or by simp
  qed

  show "\<Union> X \<union> \<Union> Y \<subseteq> \<Union> (X \<union> Y)" 
  proof (rule subsetI)
    fix x::Set
    assume "x \<in> \<Union>X \<union> \<Union>Y"
    then have **: "x \<in> \<Union>X \<or> x \<in> \<Union>Y" using union_iff_or by simp
    show "x \<in> \<Union>(X \<union> Y)"
    proof (cases "x \<in> \<Union>X")
      assume "x \<in> \<Union>X"
      then obtain z::Set where *: "z \<in> X \<and> x \<in> z" using sum_class_lemma by blast
      then have "z \<in> X \<union> Y" using union_iff_or by simp
      with * show "x \<in> \<Union>(X \<union> Y)" using sum_class_lemma by blast
      next
      assume "x \<notin> \<Union>X"
      with ** have "x \<in> \<Union>Y" by simp
      then obtain z::Set where *: "z \<in> Y \<and> x \<in> z" using sum_class_lemma by blast
      then have "z \<in> X \<union> Y" using union_iff_or by simp
      with * show "x \<in> \<Union>(X \<union> Y)" using sum_class_lemma by blast
    qed
  qed
qed

lemma Ex4_12_n: "\<Union>(X\<inter>Y) \<subseteq> (\<Union>X) \<inter> (\<Union>Y)"
proof (rule subsetI)
  fix x::Set
  assume "x \<in> \<Union>(X \<inter> Y)"
  then obtain z::Set where "z \<in> X \<inter> Y \<and> x \<in> z" using sum_class_lemma by blast
  then show "x \<in> \<Union>X \<inter> \<Union>Y" using B2 sum_class_lemma by auto
qed

lemma Ex4_12_o: "Z = Inv(Y) \<longrightarrow> Inv(Z) = Y \<inter> (\<V>\<^sup>2)"
proof 
  assume assm: "Z = Inv(Y)"
  have "Z \<subseteq> (\<V>\<^sup>2)"
  proof (rule subsetI)
    fix x::Set
    assume "x \<in> Z"
    show "x \<in> (\<V>\<^sup>2)" using Ex4_9_b \<open>Rep_Set x \<in> Z\<close> assm cartesian_product_lemma comprehensionE 
      inverse_relation_def cartesian_definable comprehensionI n_product_remark1 by fastforce 
  qed
  have a: "\<langle>x,y\<rangle> \<in> Z \<longleftrightarrow> (\<langle>y,x\<rangle> \<in> (Y \<inter> (\<V>\<^sup>2)))" 
    using B2 Ex4_9_b assm cartesian_product_lemma inverse_relation_lemma square by auto 
  show "Inv(Z) = Y \<inter> (\<V>\<^sup>2)" 
  proof (rule equalityI)
    show "Inv(Z) \<subseteq> Y \<inter> (\<V>\<^sup>2)"
    proof (rule subsetI)
      fix x::Set
      assume "x\<in>Inv(Z)"
      show "x\<in>Y \<inter> (\<V>\<^sup>2)" using B2 Ex4_9_b \<open>Rep_Set x \<in> Inv Z\<close> assm cartesian_product_lemma 
        comprehensionE inverse_relation_def inverse_relation_lemma square by fastforce 
    qed
    show "Y \<inter> (\<V>\<^sup>2) \<subseteq> Inv(Z)"
    proof (rule subsetI)
      fix x::Set
      assume "x\<in>Y \<inter> (\<V>\<^sup>2)"
      show "x\<in>Inv(Z)" using B2 \<open>Rep_Set x \<in> Y \<inter> (\<V>\<^sup>2)\<close> assm cartesian_product_lemma 
        inverse_relation_lemma square by auto 
    qed
  qed
qed

lemma Ex4_12_p: "Rel(\<I>) \<and> Inv(\<I>) = \<I>"
proof
  show r: "Rel(\<I>)"
  proof (simp add: relation_predicate_def)
    show "\<I> \<subseteq> (\<V>\<^sup>2)"
    proof (rule subsetI)
      fix x::Set
      assume assm: "x\<in>\<I>"
      show "x\<in>(\<V>\<^sup>2)"
      proof -
        from assm obtain u::Set where "x = \<langle>u,u\<rangle>" using Rep_Set_inject identity_relation_lemma by auto
        from this show "x\<in>(\<V>\<^sup>2)" using square Ex4_9_b cartesian_product_lemma by auto
      qed
    qed  
  qed

  show "Inv(\<I>) = \<I>"
  proof (rule equalityI)
    show "Inv(\<I>)\<subseteq>\<I>"
    proof (rule subsetI)
      fix x::Set
      assume assm1: "x\<in>Inv(\<I>)"
      from this have "Rel(Inv(\<I>))" by (metis Ex4_10_c Ex4_12_o \<open>Rel \<I>\<close> relation_predicate_def)
      from this have "x\<in>\<V>\<times>\<V>" using assm1 relation_predicate_def subset square by auto
      from this assm1 obtain z y where "x = \<langle>y,z\<rangle>" using Rep_Set_inject cartesian_product_lemma by auto
      from this assm1 have "\<langle>z,y\<rangle>\<in>\<I>" by (simp add: inverse_relation_lemma)
      from this have "z = y" by (metis Class_Ex_Equals1 identity_relation_lemma)
      from this have "x = \<langle>y,y\<rangle>" by (simp add: \<open>x = \<langle>y, z\<rangle>\<close>)
      then show "x\<in>\<I>" using \<open>Rep_Set \<langle>z, y\<rangle> \<in> \<I>\<close> \<open>z = y\<close> by blast
    qed
    show "\<I>\<subseteq>Inv(\<I>)"
    proof (rule subsetI)
      fix x::Set
      assume assm2: "x\<in>\<I>"
      show "x\<in>Inv(\<I>)"
      proof -
        from r assm2 obtain z where "x=\<langle>z,z\<rangle>" using Rep_Set_inject identity_relation_lemma by auto
        with assm2 show "x\<in>Inv(\<I>)" by (simp add: inverse_relation_lemma)
      qed
    qed
  qed
qed

lemma Ex4_12_q: "\<P>(\<emptyset>) = {\<emptyset>}"
proof (rule equalityI)
  show "\<P>(\<emptyset>) \<subseteq> {\<emptyset>}"
  proof (rule subsetI)
    fix x::Set
    assume "x \<in> \<P>(\<emptyset>)"
    with power_class_lemma have "x \<subseteq> \<emptyset>" by simp
    then have "x = \<emptyset>" by (simp add: Ex4_10_c Ex4_10_i Rep_Set_inject)
    then show "x \<in> {\<emptyset>}" by (simp add: pairing)
  qed
  show "{\<emptyset>} \<subseteq> \<P>(\<emptyset>)" by (metis Ex4_12_b Ex4_12_g)
qed


lemma Ex4_12_r: "\<P>({\<emptyset>}) = {\<emptyset>, {\<emptyset>}}"
proof (rule equalityI)
  show "\<P>({\<emptyset>}) \<subseteq> {\<emptyset>, {\<emptyset>}}"
  proof (rule subsetI)
    fix x::Set
    assume "x \<in> \<P>({\<emptyset>})"
    then have *: "x \<subseteq> {\<emptyset>}" using power_class_lemma by simp
    have "x = \<emptyset> \<or> x = {\<emptyset>}" 
    proof (rule ccontr)
      assume "\<not>(x = \<emptyset> \<or> x = {\<emptyset>})"
      then have **: "x \<noteq> \<emptyset> \<and> x \<noteq> {\<emptyset>}" by simp
      then obtain z where ***: "z \<in> x" by (metis Rep_Set_inverse empty_set extensionality) 
      with * ** have "z \<noteq> \<emptyset>" by (metis Rep_Set_inject equalityI pairing subsetI) 
      from * *** have "z = \<emptyset>" using pairing subclass'_def by blast
      with \<open>z \<noteq> \<emptyset>\<close> show "False" ..
    qed
    then show "x \<in> {\<emptyset>, {\<emptyset>}}" using pairing by auto
  qed
  show "{\<emptyset>, {\<emptyset>}} \<subseteq> \<P>({\<emptyset>})"
  proof (rule subsetI)
    fix x::Set
    assume "x \<in> {\<emptyset>, {\<emptyset>}}"
    then have "x = \<emptyset> \<or> x = {\<emptyset>}" by (simp add: Rep_Set_inject pairing)
    then have "x \<subseteq> {\<emptyset>}" by (metis Ex4_12_a Ex4_12_b Ex4_12_g Ex4_12_q)
    then show "x \<in> \<P>({\<emptyset>})" by (simp add: power_class_lemma)
  qed
qed

lemma Ex4_12_s: "\<forall>x y. x \<times> y \<subseteq> \<P>(\<P>(x \<union> y))"
proof
  fix x
  show " \<forall>y. x \<times> y \<subseteq> \<P>(\<P>(x \<union> y))"
  proof
    fix y
    show "x \<times> y \<subseteq> \<P>(\<P>(x \<union> y))"
    proof (rule subsetI)
      fix z
      assume "z \<in> x \<times> y"
      then obtain z1 z2 where "z = \<langle>z1, z2\<rangle>" "z1 \<in> x" "z2 \<in> y"
        using cartesian_product_lemma by blast
      then have "{z1} \<subseteq> x \<union> y" 
        by (metis Ex4_9_a pairing subsetI)
      then have "{z1} \<in> \<P>(x \<union> y)" using power_class_lemma by simp
      from \<open>z1 \<in> x\<close> \<open>z2 \<in> y\<close> have "{z1, z2} \<subseteq> x \<union> y" 
        using Ex4_9_a pairing subsetI by presburger
      then have "{z1, z2} \<in> \<P>(x \<union> y)" using power_class_lemma by simp
      with \<open>{z1} \<in> \<P>(x \<union> y)\<close> have "{{z1},{z1,z2}} \<subseteq> \<P>(x \<union> y)"
        using pairing subsetI by presburger
      then have "{{z1},{z1,z2}} \<in> \<P>(\<P>(x \<union> y))" 
        using power_class_lemma by simp
      with \<open>z = \<langle>z1,z2\<rangle>\<close> show "z \<in> \<P>(\<P>(x \<union> y))" using ordered_pair_def by simp
    qed
  qed
qed

lemma Ex4_12_t: "Rel(Y) \<longrightarrow> Y \<subseteq> dom(Y) \<times> ran(Y)" 
proof (rule impI)
  assume a: "Rel(Y)"
  show "Y \<subseteq> dom(Y) \<times> ran(Y)"
  proof (rule subsetI)
    fix x::Set
    assume "x\<in>Y"
    from this obtain y z where "\<langle>y, z\<rangle> = x" using Rep_Set_inject a cartesian_product_lemma 
      square relation_predicate_def subclass'_def by auto
    from this have "y\<in>dom(Y)" using B4 \<open>Rep_Set x \<in> Y\<close> by blast 
    moreover have "z\<in>ran(Y)" using \<open>Rep_Set x \<in> Y\<close> \<open>\<langle>y, z\<rangle> = x\<close> range_lemma by auto
    with a \<open>y\<in>dom(Y)\<close> show "x \<in> dom(Y) \<times> ran(Y)" using \<open>\<langle>y, z\<rangle> = x\<close> cartesian_product_lemma
      by blast
  qed
qed

(* page 236 *)

axiomatization 
where sum_set: 
  "\<forall>x::Set. \<exists>y::Set. \<forall>u::Set. (u\<in>y \<longleftrightarrow> (\<exists>v::Set. u\<in>v \<and> v\<in>x))"
                                          
lemma sum_set_remark: "\<forall>x::Set. (\<Union>x is a set)"
proof                                     
  fix x::Set
  obtain y::Set where "\<forall>u::Set.(u\<in>y \<longleftrightarrow> (\<exists>v::Set. u\<in>v \<and> v\<in>x))" using sum_set by blast
  hence "y=\<Union>x" by (simp add: set_extensionality sum_class_lemma)   
  thus "(\<Union>x) is a set" by (metis Ex4_9_b universe) 
qed

(* Not sure how and if this will be used, but it is in Mendelson.
   I commented it out because it's causing my Isabelle2016 to crash.
   Experiment further. *)
(*abbreviation union_indexed :: "Set \<Rightarrow> Set" ("(\<Union>\<^sub>v\<^sub>\<in>\<^sub>_ v)")
  where "\<Union>\<^sub>v\<^sub>\<in>\<^sub>x v \<equiv> x"*)

lemma Ex4_13_a: "\<forall>x::Set. \<forall>y::Set. (\<Union>{x,y} = x\<union>y)"
proof
  fix x::Set
  show "\<forall>y::Set. (\<Union>{x,y} = x\<union>y)"
  proof
    fix y::Set
    show "\<Union>{x,y} = x\<union>y"
    proof (rule equalityI)
      show "\<Union>{x,y} \<subseteq> x\<union>y"
      proof (rule subsetI)
        fix xa::Set
        assume "xa \<in> \<Union>{x,y}"
        then show "xa \<in> x\<union>y" using pairing sum_class_lemma union_iff_or by auto
      qed
      show "x\<union>y \<subseteq> \<Union>{x,y}"
      proof (rule subsetI)
        fix xa::Set
        assume "xa \<in> x\<union>y"
        then show "xa \<in> \<Union>{x,y}" using pairing sum_class_lemma union_iff_or by auto
      qed
    qed
  qed
qed

lemma Ex4_13_b: "\<forall>x::Set. \<forall>y::Set. set(x\<union>y)"
proof
  fix x::Set
  show "\<forall>y::Set. set(x\<union>y)"
  proof
    fix y::Set
    have "set({x,y})" using Ex4_9_b set_predicate_def by auto
    then have "\<exists>z::Set. \<forall>u::Set. (u\<in>z \<longleftrightarrow> (\<exists>v::Set. u\<in>v \<and> v\<in>{x,y}))" using sum_set by simp
    then obtain z::Set where "\<forall>u::Set. (u\<in>z \<longleftrightarrow> (\<exists>v::Set. u\<in>v \<and> v\<in>{x,y}))" by blast
    then have "\<forall>u::Set. (u\<in>z \<longleftrightarrow> u\<in>\<Union>({x,y}))" using sum_class_lemma by blast
    then have "z=\<Union>({x,y})" by (simp add: set_extensionality)
    then have "set(\<Union>{x,y})" by (metis Ex4_9_b set_predicate_def)
    then show "set(x\<union>y)" using Ex4_13_a by auto
  qed
qed

lemma Ex4_13_c: "\<forall>x::Set. (\<Union>{x} = x)"
by (simp add: Ex4_10_h Ex4_13_a)

lemma Ex4_13_d: "\<forall>x::Set. \<forall>y::Set. (\<Union>\<langle>x,y\<rangle> = {x, y})"
proof
  fix x::Set
  show "\<forall>y::Set. (\<Union>\<langle>x,y\<rangle> = {x, y})"
  proof
    fix y::Set
    show "\<Union>\<langle>x,y\<rangle> = {x, y}"
    proof (rule equalityI)
      show "\<Union>\<langle>x,y\<rangle> \<subseteq> {x, y}"
      proof (rule subsetI)
        fix xa::Set
        assume "xa \<in> \<Union>\<langle>x,y\<rangle>"
        then show "xa \<in> {x, y}" using ordered_pair_def pairing sum_class_lemma by auto
      qed

      show "{x, y} \<subseteq> \<Union>\<langle>x,y\<rangle>"
      proof (rule subsetI)
        fix xa
        assume "xa \<in> {x, y}"
        then show "xa \<in> \<Union>\<langle>x,y\<rangle>" by (metis ordered_pair_def pairing sum_class_lemma)
      qed
    qed
  qed
qed

(* Here goes Exercise 4.14 *)

axiomatization 
where power_set: 
  "\<forall>x::Set. \<exists>y::Set. \<forall>u::Set. (u\<in>y \<longleftrightarrow> u\<subseteq>x)"

(* The remark right after Axiom W: *)
lemma power_set_lemma: "\<forall>x::Set. (\<P>(x) is a set)"
proof
  fix x::Set
  show "set(\<P>(x))"
  proof -
    have "\<exists>y::Set. \<forall>u::Set. (u\<in>y \<longleftrightarrow> u\<subseteq>x)" using power_set by blast
    then obtain y::Set where *: "\<forall>u::Set. (u\<in>y \<longleftrightarrow> u\<subseteq>x)" by blast
    have "\<forall>u::Set. (u \<in> \<P>(x)) \<longleftrightarrow> (u \<subseteq> x)" by (simp add: power_class_lemma)
    then have "\<forall>u::Set. u\<in>\<P>(x) \<longleftrightarrow> u\<in>y" using * by simp
    then have "\<P>(x) = y" by (simp add: set_extensionality)
    then show "set(\<P>(x))" using Ex4_9_b universe by auto 
  qed
qed

axiomatization  (* comprehension axiom if we use a definable class Y *)
where subsets:
  "\<forall>x::Set. \<forall>Y. \<exists>z::Set. \<forall>u::Set. (u\<in>z \<longleftrightarrow> u\<in>x \<and> u\<in>Y)"
-- "combined with the class existence theorem, this is the axiom (not axiom schema) of 
    comprehension."

(* page 237 *)

text{* \textbf{FOMUS workshop exercise:} *}

lemma Cor4_6_a: "\<forall>x::Set. \<forall>Y. (x\<inter>Y is a set)" 
  -- "The intersection of a set and a class is a set."
sorry


text{* \textbf{FOMUS workshop exercise:} *}

lemma Cor4_6_b: "\<forall>x::Set. \<forall>Y. (Y\<subseteq>x \<longrightarrow> set(Y))"
  -- "A subclass of a set is a set."
sorry

(*  Here goes Cor4_6_c. *)

lemma Ex4_15_a: "\<forall>x::Set. (set(dom x) \<and> set(ran x))"

proof (rule allI, rule conjI)
  fix x::Set
  have *: "dom(x) \<subseteq> \<Union>(\<Union>x)" 
  proof (rule subsetI) 
    fix y::Set
    assume "y \<in> dom(x)"
    hence "\<exists>z. (\<langle>y,z\<rangle> \<in> x)" by (simp add: B4)
    thus "y\<in>\<Union>(\<Union>x)" by (metis ordered_pair_def pairing sum_class_lemma) 
  qed
  have "(\<Union>x) is a set" using sum_set_remark by auto
  thus "(dom(x)) is a set" using * 
    by (metis Abs_Set_inverse Cor4_6_b mem_Collect_eq sum_set_remark universe) 
next -- "similar proof"
  fix x::Set
  have *: "ran(x) \<subseteq> \<Union>(\<Union>x)" 
  proof (rule subsetI) 
    fix y::Set
    assume "y \<in> ran(x)"
    hence "\<exists>z. (\<langle>z,y\<rangle> \<in> x)" by (simp add: range_lemma)
    thus "y \<in> \<Union>(\<Union>x)" by (metis ordered_pair_def pairing sum_class_lemma) 
  qed
  thus "(ran(x)) is a set" using * 
    by (metis Abs_Set_inverse Cor4_6_b mem_Collect_eq sum_set_remark universe) 
qed

lemma Ex4_15_b: "\<forall>x::Set. \<forall>y::Set. set(x \<times> y)"
proof
  fix x::Set
  show "\<forall>y::Set. set(x \<times> y)"
  proof
    fix y::Set
    have #: "(x \<times> y) \<subseteq> \<P>(\<P>(x \<union> y))" using Ex4_12_s by simp
    have *: "set(x\<union>y)" by (simp add: Ex4_13_b)
    then have "set(\<P>(x \<union> y))" using power_set_lemma by (metis CollectI Rep_Set_cases universe)
    then have "set(\<P>(\<P>(x \<union> y)))" using power_set_lemma by (metis CollectI Rep_Set_cases universe)
    then show "set(x \<times> y)" using # Cor4_6_b by (metis CollectI Rep_Set_cases universe)
  qed
qed

lemma Ex4_15_c: "set(dom(Y)) \<and> set(ran(Y)) \<and> Rel(Y) \<longrightarrow> set(Y)"
proof
  assume *: "set(dom(Y)) \<and> set(ran(Y)) \<and> Rel(Y)"
  then have 1: "Y\<subseteq>(dom Y)\<times>(ran Y)" and #: "set(dom(Y))" and ##: "set(ran(Y))"
    using Ex4_12_t by (simp,simp,simp)
  then have "set((dom Y)\<times>(ran Y))" using Ex4_15_b # ## by (metis CollectI Rep_Set_cases universe)
  from 1 and this show "set(Y)" using Cor4_6_b by (metis CollectI Rep_Set_cases universe)
qed

lemma Ex4_15_d: "Pr(Y) \<and> Y\<subseteq>X \<longrightarrow> Pr(X)"
proof 
  assume "Pr(Y) \<and> Y\<subseteq>X"
  then have 1: "Pr(Y)" and 2: "Y\<subseteq>X" by (rule conjunct1, rule conjunct2)
  show "Pr(X)"
  proof (rule ccontr)
    assume "~Pr(X)"
    then have "set(X)" by (simp add: proper_class_predicate_def)
    then have "set(Y)" using 2 Cor4_6_b by (metis CollectI Rep_Set_cases universe)
    then show "False" using 1 by (simp add: proper_class_predicate_def)
  qed
qed

lemma int_class_definable[defining]: "definable(\<lambda>x::Set. (\<forall>v::Set. v\<in>X \<longrightarrow> x\<in>v))"
unfolding definable_def
proof
  let ?f = "\<lambda>x::Set. (\<forall>v::Set. v\<in>X \<longrightarrow> x\<in>v)"
  def \<phi> \<equiv> "(FAll 10 (FImp (FBelongs (FVar 10) (FConst X))
                           (FBelongs (FVar 0) (FVar 10))))"
  show "\<forall>i. (FOL_True \<phi> i \<longleftrightarrow> ?f(i(0)))"  
     unfolding \<phi>_def using "FOL_True.simps" "FOL_Eval.simps" Update_def by auto
qed

definition
  int_class :: "Class \<Rightarrow> Class" ("\<Inter>")
  where "\<Inter>X = { x::Set \<bar> (\<forall>v::Set. v\<in>X \<longrightarrow> x\<in>v)}"

lemma int_class_lemma: "\<forall>x::Set. x \<in> \<Inter>X \<longleftrightarrow> (\<forall>v::Set. v\<in>X \<longrightarrow> x\<in>v)"
by (simp add: class_comprehension_property int_class_def int_class_definable)


text{* \textbf{FOMUS workshop exercise:} **  *}

lemma Prop4_7_a: "\<forall>x::Set. x\<in>X \<longrightarrow> (\<Inter>X \<subseteq> x)"
sorry

lemma Prop4_7_b: "X \<noteq> \<emptyset> \<longrightarrow> set(\<Inter>X)"
proof
  assume "X\<noteq>\<emptyset>"
  then obtain x::Set where "x\<in>X" using empty_set Rep_Set_inject set_extensionality by blast
  then have "\<Inter>X\<subseteq>x" using Prop4_7_a by simp
  then show "set(\<Inter>X)" using Cor4_6_b by simp
qed

lemma Prop4_7_c: "\<Inter>\<emptyset> = \<V>"
proof (rule equalityI)
  show "\<Inter>\<emptyset> \<subseteq> \<V>"
  proof (rule subsetI)
    fix x::Set
    assume "x\<in>\<Inter>\<emptyset>"
    show "x\<in>\<V>" using Ex4_9_b by auto
  qed

  show "\<V> \<subseteq> \<Inter>\<emptyset>"
  proof (rule subsetI)
    fix x::Set
    assume "x\<in>\<V>"
    show "x\<in>\<Inter>\<emptyset>" by (simp add: empty_set int_class_lemma)
  qed
qed

(*  page 238 *)

lemma Ex4_16_a: "\<Inter>{x, y} = x\<inter>y"
proof (rule equalityI)
  show "\<Inter>{x, y} \<subseteq> x\<inter>y"
  proof (rule subsetI)
    fix xa::Set
    assume "xa\<in>\<Inter>{x, y}"
    show "xa \<in> x\<inter>y" using B2 \<open>Rep_Set xa \<in> \<Inter> (Rep_Set {x, y})\<close> int_class_lemma pairing by auto
  qed

  show "x\<inter>y \<subseteq> \<Inter>{x, y}"
  proof (rule subsetI)
    fix xa::Set
    assume "xa\<in>x\<inter>y"
    show "xa\<in>\<Inter>{x, y}" using B2 \<open>Rep_Set xa \<in> Rep_Set x \<inter> Rep_Set y\<close> int_class_lemma pairing by auto
  qed
qed

lemma Ex4_16_b: "\<Inter>{x} = x"
by (simp add: Ex4_10_g Ex4_16_a)

lemma Ex4_16_c: "X\<subseteq>Y \<longrightarrow> \<Inter>Y \<subseteq> \<Inter>X"
proof
  assume "X\<subseteq>Y"
  show "\<Inter>Y \<subseteq> \<Inter>X"
  proof (rule subsetI)
    fix x::Set
    assume "x\<in>\<Inter>Y"
    show "x\<in>\<Inter>X" using \<open>Rep_Set x \<in> \<Inter> Y\<close> \<open>X \<subseteq> Y\<close> int_class_lemma subset by blast
  qed
qed

definition Fnc :: "Class \<Rightarrow> bool" ("(_ is a function)" [71] 70)
  where "Fnc(X) == Rel(X) \<and> (\<forall>x y z::Set. (\<langle>x,y\<rangle>\<in>X \<and> \<langle>x,z\<rangle>\<in>X) \<longrightarrow> y=z)"

definition function_from_to :: "Class \<Rightarrow> Class \<Rightarrow> Class \<Rightarrow> bool" 
  ("(_ is a function from _ to _)" 70)
  where "X is a function from Y to Z == Fnc(X) \<and> (dom(X) = Y) \<and> (ran(X) \<subseteq> Z)"
notation function_from_to ("(_: _ \<rightarrow> _)"  70)

definition
  restriction :: "Class \<Rightarrow> Class \<Rightarrow> Class"  (infixl "\<restriction>" 80)
  where "(X\<restriction>Y) \<equiv> X\<inter>(Y\<times>\<V>)" 
--"Warning, Mendelson defines this X\<down>Y, with a curly arrow and the X and Y switched. We use the 
   modern ."

definition Fnc1 :: "Class \<Rightarrow> bool" ("(_ is a 1-1 function)")
  where "Fnc1(X) == Fnc(X) \<and> Fnc(Inv(X))"
notation   Fnc1 ("(_ is an injection)" 70)

(* "onto" is defined in Mendelson's book introduction. I add this here as it fits 
           after the injection, and I also add bijection. *)

definition surjection_from_onto :: "Class \<Rightarrow> Class \<Rightarrow> Class \<Rightarrow> bool" 
  ("(_ is a surjection from _ onto _)")
  where "(F is a surjection from A onto B) \<longleftrightarrow> (F:A\<rightarrow>B) \<and> (ran(F) = B)"

definition bijection_from_to :: "Class \<Rightarrow> Class \<Rightarrow> Class \<Rightarrow> bool"
  ("(_) is a bijection from (_) to (_)")
  where "(F is a bijection from A to B) \<longleftrightarrow> (F:A\<rightarrow>B) \<and> (F is an injection) \<and> (ran(F) = B)"

(* The following definition might be buggy*)

(* The following used to be called image, when in fact it is the value_of the 
           function X at Y. The definition below this one is the one of image. *)
definition 
  value_of :: "Class \<Rightarrow> Class \<Rightarrow> Set"  (infixl "\<acute>" 80)
  where "X\<acute>Y == (if   (\<exists>!u::Set. (\<langle>Abs_Set Y, u\<rangle> \<in> X)) 
                 then THE u::Set. (\<langle>Abs_Set Y, u\<rangle> \<in> X)
                 else \<emptyset>)"

lemma value_of_lemma: 
  fixes X::Class
  fixes y::Set
  assumes "X is a function"
  and "y\<in>dom(X)"
  shows "\<exists>z::Set. \<langle>y,z\<rangle>\<in>X"
using B4 assms(2) by auto
                            

abbreviation set_value_of :: "Set \<Rightarrow> Set \<Rightarrow> Set" 
(* Since we can't overload the \acute symbol, is there any benefit on keeping this 
           definition? *)
  where "set_value_of x y \<equiv> value_of x y" 

definition 
  image :: "Class \<Rightarrow> Class \<Rightarrow> Class"  (infixl "\<hungarumlaut>" 80) --"This symbol is called hungarumlaut."
where "(X\<hungarumlaut>Y) \<equiv> ran(X\<restriction>Y)"

lemma Ex4_17_a: "Fnc(X) \<and> (y::Set)\<in>dom(X) \<longrightarrow> (\<forall>z::Set. (X\<acute>y) = z \<longleftrightarrow> \<langle>y,z\<rangle>\<in>X)" 
proof (rule impI)
  assume *: "X is a function \<and> Rep_Set y \<in> dom X"
  have **:  "\<forall> b c d::Set. (\<langle>d,b\<rangle>\<in>X \<and> \<langle>d,c\<rangle>\<in>X) \<longrightarrow> b=c" using * by (simp add: Fnc_def) 
  hence ***: "\<forall>b c::Set. (\<langle>y,b\<rangle>\<in>X \<and> \<langle>y,c\<rangle>\<in>X) \<longrightarrow> b=c" by auto
  obtain u::Set where u: "\<langle>y,u\<rangle>\<in>X" using value_of_lemma * by auto
  hence u': "\<forall>b::Set. (\<langle>y,b\<rangle>\<in>X \<and> \<langle>y,u\<rangle>\<in>X) \<longrightarrow> b=u" using ** by auto
  hence ****: "\<exists>!u. (\<langle>y,u\<rangle>\<in>X)" using u by blast 
  show "\<forall>z::Set. (X\<acute>y) = z \<longleftrightarrow> \<langle>y,z\<rangle>\<in>X" 
  proof (rule allI, rule iffI)
    fix z::Set
    assume "(X\<acute>y) = z"
    hence "z = (X\<acute>y)" .. --"Strangely, the proof below fails without this step."
    hence "z = (if (\<exists>!u::Set. (\<langle>y, u\<rangle> \<in> X)) 
                          then THE u::Set. (\<langle>y, u\<rangle> \<in> X)
                          else \<emptyset>)"  unfolding value_of_def using * by (simp add: Rep_Set_inverse) 
    hence "z = (THE u::Set. (\<langle>y, u\<rangle> \<in> X))" using **** by auto
    hence "\<langle>y,z\<rangle>\<in>X" using the1I2 **** Rep_Set_inverse by metis 
    thus "X \<acute> Rep_Set y = z \<Longrightarrow> Rep_Set \<langle>y, z\<rangle> \<in> X" by auto
  next 
    fix z::Set
    assume "\<langle>y,z\<rangle>\<in>X"
    hence "(THE u::Set. (\<langle>y, u\<rangle> \<in> X)) = z" using Rep_Set_inverse by (metis u' u the_equality)
    thus "X\<acute>y = z" unfolding value_of_def using Abs_Set_inverse Rep_Set_inverse **** the_equality 
      by auto 
  qed
qed

lemma Ex4_17_b: "X is a function \<and> Y \<subseteq> dom(X) \<longrightarrow> 
                 ((X\<restriction>Y) is a function \<and> (dom(X\<restriction>Y) = Y) \<and> (\<forall>y::Set. y\<in>Y \<longrightarrow> X\<acute>y = (X\<restriction>Y)\<acute>y))"
proof
  assume *: "X is a function \<and> Y \<subseteq> dom(X)"
  show "(X\<restriction>Y) is a function \<and> (dom(X\<restriction>Y) = Y) \<and> (\<forall>y::Set. y\<in>Y \<longrightarrow> (X\<acute>y = (X\<restriction>Y)\<acute>y))"
  proof
    show 1: "(X\<restriction>Y) is a function"
    proof (unfold Fnc_def)
      show "(X \<restriction> Y) is a relation \<and> (\<forall>x y z::Set. \<langle>x,y\<rangle>\<in>(X\<restriction>Y) \<and> \<langle>x,z\<rangle>\<in>(X\<restriction>Y) \<longrightarrow> y=z)"
      proof
        show "(X \<restriction> Y) is a relation" using * by (metis Ex4_10_c Ex4_10_e Ex4_10_k Ex4_12_h 
          relation_predicate_def restriction_def square) 
        show "\<forall>x y z::Set. \<langle>x,y\<rangle>\<in>(X\<restriction>Y) \<and> \<langle>x,z\<rangle>\<in>(X\<restriction>Y) \<longrightarrow> y=z"
          using * by (metis Fnc_def notin_inter_mono restriction_def)
      qed
    qed
    show "(dom(X\<restriction>Y) = Y) \<and> (\<forall>y::Set. y\<in>Y \<longrightarrow> (X\<acute>y = (X\<restriction>Y)\<acute>y))" 
    proof
      show 2: "dom(X\<restriction>Y) = Y"
      proof (unfold set_extensionality)
        show "\<forall>x::Set. x\<in>dom(X\<restriction>Y) \<longleftrightarrow> x\<in>Y" 
        proof
          fix x::Set
          have "x\<in>dom(X\<restriction>Y) \<longleftrightarrow> (\<exists>v::Set. (\<langle>x, v\<rangle>\<in>X\<inter>(Y\<times>\<V>)))" by (simp add: B4 restriction_def) 
          then have "x\<in>dom(X\<restriction>Y) \<longleftrightarrow> (\<exists>v::Set. (\<langle>x, v\<rangle>\<in>X \<and> \<langle>x, v\<rangle>\<in>(Y\<times>\<V>)))" using B2 by auto
          then have #: "x\<in>dom(X\<restriction>Y) \<longleftrightarrow> (\<exists>v::Set. (\<langle>x, v\<rangle>\<in>X \<and> \<langle>x, v\<rangle>\<in>(Y\<times>\<V>) \<and> x\<in>Y))"
            by (metis Prop4_3 Rep_Set_inject cartesian_product_lemma)
          from * have "\<forall>x2::Set. (x2\<in>Y \<longleftrightarrow> (\<exists>w::Set. \<langle>x2,w\<rangle>\<in>X) \<and> x2\<in>Y)"
            using B4 subclass'_def by blast
          then show "x\<in>dom(X\<restriction>Y) \<longleftrightarrow> x\<in>Y" using # Ex4_9_b cartesian_product_lemma by blast 
        qed
      qed
      show "\<forall>y::Set. y\<in>Y \<longrightarrow> (X\<acute>y = (X\<restriction>Y)\<acute>y)"
        using * 1 2 by (metis B4 Ex4_17_a notin_inter_mono restriction_def)
    qed
  qed
qed

lemma Ex4_17_c: "Fnc(X) \<longrightarrow> 
                (Fnc1(X) \<longleftrightarrow> (\<forall>y z::Set. (y\<in>dom(X) \<and> z\<in>dom(X) \<and> y\<noteq>z) \<longrightarrow> (X\<acute>y \<noteq> X\<acute>z)))"
proof (rule impI)
  fix X::Class
  assume "Fnc(X)"
  from \<open>Fnc(X)\<close> have *: "Fnc1(X) \<longleftrightarrow> Fnc(Inv(X))" by (simp add: Fnc1_def)
  from \<open>Fnc(X)\<close> have **: "Rel(Inv(X))" by (metis Ex4_10_c Ex4_12_o Fnc_def relation_predicate_def) 
  show "Fnc1(X) \<longleftrightarrow> (\<forall>y z::Set. ((y\<in>dom(X) \<and> z\<in>dom(X) \<and> y\<noteq>z) \<longrightarrow> X\<acute>y \<noteq> X\<acute>z))"
  proof (rule iffI, rule allI, rule allI, rule impI)
    assume "Fnc1(X)"
    fix y z::Set
    assume 0: "y\<in>dom(X) \<and> z\<in>dom(X) \<and> y\<noteq>z"
    show "X\<acute>y \<noteq> X\<acute>z"
    proof (rule ccontr)
      assume "\<not>(X\<acute>y \<noteq> X\<acute>z)" 
      hence 1: "X\<acute>y = X\<acute>z" by simp
      then obtain u::Set where 2: "\<langle>u,X\<acute>y\<rangle>\<in>X" and 3: "\<langle>u,X\<acute>z\<rangle>\<in>X"
        unfolding Fnc1_def Fnc_def by (metis "0" Ex4_17_a \<open>X is a function\<close>) 
      hence "y=z" by (metis "*" "0" B4 Ex4_17_a Fnc_def 
                                \<open>X is a function\<close> \<open>X is an injection\<close> inverse_relation_lemma)  
      thus False using 0 by simp
    qed
    next
    assume 0: "\<forall>y z::Set. ((y\<in>dom(X) \<and> z\<in>dom(X) \<and> y\<noteq>z) \<longrightarrow> X\<acute>y \<noteq> X\<acute>z)"
    have "\<forall>x y z::Set. (\<langle>x,y\<rangle>\<in>(Inv(X)) \<and> \<langle>x,z\<rangle>\<in>(Inv(X))) \<longrightarrow> (y=z)"  
    proof (rule allI, rule allI, rule allI, rule impI)
      fix x y z::Set
      assume 1: "\<langle>x,y\<rangle>\<in>Inv(X) \<and> \<langle>x,z\<rangle>\<in>Inv(X)" 
      hence "\<langle>y,x\<rangle>\<in>X \<and> \<langle>z,x\<rangle>\<in>X" using inverse_relation_lemma by simp
      thus "y=z" by (metis "0" B4 Ex4_17_a Fnc_def \<open>Fnc(X)\<close>) 
    qed
    thus "X is an injection" by (simp add: "*" "**" Fnc_def)         
  qed
qed

lemma Ex4_17_d: "Fnc(X) \<and> Y\<subseteq>dom(X) \<longrightarrow> (\<forall>z::Set. z\<in>X\<hungarumlaut>Y \<longleftrightarrow> (\<exists>y::Set. y\<in>Y \<and> X\<acute>y = z))"
proof
  assume *: "Fnc(X) \<and> Y\<subseteq>dom(X)"
  show "\<forall>z::Set. z\<in>X\<hungarumlaut>Y \<longleftrightarrow> (\<exists>y::Set. y\<in>Y \<and> X\<acute>y = z)"
  proof
    fix z::Set
    have "z\<in>X\<hungarumlaut>Y \<longleftrightarrow> (\<exists>v::Set. \<langle>v,z\<rangle>\<in>X \<and> \<langle>v,z\<rangle>\<in>(Y\<times>\<V>))"
      by (simp add: image_def range_lemma restriction_def B2)
    then have "z\<in>X\<hungarumlaut>Y \<longleftrightarrow> (\<exists>v::Set.\<langle>v,z\<rangle>\<in>X \<and> v\<in>Y)"
      using Ex4_9_b by (metis Prop4_3 Rep_Set_inject cartesian_product_lemma)  
    then have "z\<in>X\<hungarumlaut>Y \<longleftrightarrow> (\<exists>v::Set. X\<acute>v = z \<and> v\<in>Y)" using * Ex4_17_a subclass'_def by blast
    then show "z\<in>X\<hungarumlaut>Y \<longleftrightarrow> (\<exists>y::Set. y\<in>Y \<and> X\<acute>y = z)" by blast
  qed
qed

(* page 239 *)

text{* \subsection*{Axiom R - Replacement} *}

axiomatization 
where replacement: 
  "Fnc(Y) \<longrightarrow> (\<forall>x::Set. \<exists>y::Set. \<forall>u::Set. (u\<in>y \<longleftrightarrow> (\<exists>v::Set. \<langle>v,u\<rangle>\<in>Y \<and> v\<in>x)))"

text{* 
      \begin{quote}
      Axiom R asserts that, if $Y$ is a function and $x$ is a set, then the class of second
      components of ordered pairs in $Y$ whose first components are in $x$ is a set
      (or, equivalently, $ran(x\upharpoonright Y)$ is a set).  
      \end{quote} 
*}

lemma replacement_remark: 
  assumes "Y is a function"
  fixes x::Set
  shows "(ran(Y\<restriction>x)) is a set" 
 --"This is obvious for Mendelson, not for Isabelle, and Sledgehammer cannot find a proof."
proof -
  have "(\<exists>y::Set. \<forall>u::Set. (u\<in>y \<longleftrightarrow> (\<exists>v::Set. \<langle>v,u\<rangle>\<in>Y \<and> v\<in>x)))" using replacement assms by auto 
  then obtain y :: Set where "\<forall>u::Set. (u\<in>y \<longleftrightarrow> (\<exists>v::Set. \<langle>v,u\<rangle>\<in>Y \<and> v\<in>x))" by auto
  hence "\<forall>u::Set. (u\<in>y \<longleftrightarrow> (\<exists>v::Set. \<langle>v,u\<rangle>\<in>(Y\<restriction>x)))" using restriction_def
    by (metis B2 B5 Rep_Set cartesian_product_lemma mem_Collect_eq) 
  hence "\<forall>u::Set. (u\<in>y \<longleftrightarrow> (u\<in>ran(Y\<restriction>x)))" using range_lemma[where Y="(Y\<restriction>x)"] by simp
  hence "y=ran(Y\<restriction>x)" using set_extensionality by simp
  thus ?thesis by (metis Ex4_9_b universe) 
qed
   
(* Exercise 4.18 would require our theory to be build using locales. *)
 
(*
  lemma Ex4_18: Show that,  in  the presence  of  the other axioms, the replacement axiom
  (R) implies the axiom  of  subsets (S).
*)


text{* \textbf{FOMUS workshop exercise:} *}

lemma Ex4_19: "Fnc(Y) \<longrightarrow> (\<forall>x::Set. (Y\<hungarumlaut>x is a set))"
sorry


(* Exercises 4.20 and 4.21 require our theories to be build using locales. *)

(*
  lemma Ex4_20: the Show  that  axiom R is equivalent  to  the  wf 
  "Fnc(Y) \<and> set(dom(Y)) \<longrightarrow> set(ran(Y))"

  lemma Ex4_21: Show that,  in  the presence  of  all axioms except  RandS,  axiom R is
  equivalent to the conjunction  of  axiom S  and  the  wf
 "Fnc1(Y) \<and> set(dom(Y)) \<longrightarrow> set(ran(Y))"
*)

text{* \subsection*{Axiom I (Axiom of Infinity)} *}

axiomatization 
where infinity: 
  "\<exists>x::Set. (\<emptyset>\<in>x \<and> (\<forall>u::Set. (u\<in>x \<longrightarrow> (u\<union>{u})\<in>x)))"

text{* \begin{quote}
       Axiom I states that there is a set $x$ that contains 0 and such that, whenever a
       set $u$ belongs to $x$, then $u \cup \{u\}$ also belongs to $x$. Hence, for such a set $x$,
       $\{0\} \in x$, $\{0, \{0\}\}\in x$, $\{0, \{0\}, \{0, \{0\}\}\}\in x$, and so on. 
       If we let 1 stand for $\{0\}$, 2 for $\{0, 1\}$, 3 for $\{0, 1, 2\}$, ... , $n$ for 
       $\{0, 1, 2, ... , n - 1\}$, etc., then, for all ordinary integers $n > 0$, $n\in x$,
       and $0 -/=- 1, 0 -/=- 2, 1 -/=- 2, 0 -1 3, 1 f:- 3, 2 #-3, ...
       \end{quote} *}

primrec set_integer :: "nat \<Rightarrow> Set" ("int")
  where "int(0)     = Abs_Set \<emptyset>"
      | "int(Suc n) = Abs_Set (int(n)\<union>{int(n)})"


text{* \textbf{FOMUS workshop extra exercise:} *}

lemma infinity_remark: 
  "\<forall>n::nat. int(n)\<noteq>int(Suc n)" 
  and "\<exists>x::Set. \<forall>n::nat. int(n)\<in>x"
sorry 

(*
  lemma Ex_4_22_a: Prove  that  any  wf  that  implies "\<exists>X. set(X)" would, together with
  axiom  S,  imply axiom N.
*)

(*
  lemma Ex_4_22_b: Show that axiom I is equivalent  to  the following sentence  (I* ):
  "\<exists>x. ((\<exists>y. y\<in>x \<and> (\<forall>u. u\<notin>y)) \<and> (\<forall>u. u\<in>x \<longrightarrow> (u\<union>{u})\<in>x) )"
*)

(* page 240 *) 

text{* \begin{quote}
       This completes the List of axioms of NBG, and we see that NBG has only a
       finite number of axioms - namely, axiom T, axiom P (pairing), axiom N
       (null set), axion1 U (sum set), axiom W (power set), axiomS (subsets), axiom
       R (replacement), axiom 1 (infinity), and the seven class existence axioms
       (Bl)-(B7). We have also seen that axiom S is provable from the other
       axioms; it has been included here because it is of interest in the study of
       certain weaker subtheories of NBG.  Let us verify now that the usual argument 
       for Russell's paradox does not hold in NBG.
       \end{quote} *}


text{* \textbf{FOMUS workshop exercise:} *}

lemma no_Russells_paradox: 
    fixes Y :: Class
  assumes "Y = { x \<bar> x\<notin>x }"
    shows "Y is not a set"
proof (rule ccontr)
  have "definable(\<lambda>x. x\<notin>x)"
  sorry
  then have *: "\<forall>x::Set. x\<in>Y \<longleftrightarrow> x\<notin>x" by (simp add: assms class_comprehension_property)
  assume "\<not>\<not>(Y is a set)" 
  then have "Y\<in>Y \<longleftrightarrow> Y\<notin>Y" by (metis DomainpE Set.domain_eq Set.pcr_cr_eq * cr_Set_def universe)
  hence "Y\<in>Y \<and> Y\<notin>Y" by simp
  thus False by simp
qed



text{* Thus, in NBG, the argument for Russell's paradox merely shows that Russell's 
       class Y is a proper class, not a set. NBG will avoid the paradoxes of Cantor and
       Burali-Forti in a similar way.*}

text{* \textbf{FOMUS workshop extra exercise:} *}

lemma Ex4_23: "\<not>set(\<V>)" 
sorry


end
