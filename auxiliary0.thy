theory auxiliary0
imports axioms_base
begin


text{* Proving rules for proofs about class equality. *}

lemma equalityI: "\<lbrakk>X \<subseteq> Y; Y \<subseteq> X\<rbrakk> \<Longrightarrow> X = Y"
by (simp add: Prop4_1_a)

lemma equalityE: "X = Y \<Longrightarrow> X \<subseteq> Y"
by (simp add: Prop4_1_a)

lemma Ex_Set: "\<lbrakk>\<And>u :: Set. u \<in> X \<longleftrightarrow> u \<in> Y\<rbrakk> \<Longrightarrow> X = Y"
by (metis Abs_Set_inverse extensionality mem_Collect_eq set_predicate_def universe)


text{* Two proving rules and a lemma about subclasses *} 

lemma subsetI: "(\<And>x::Set. x \<in> X \<Longrightarrow> x \<in> Y) \<Longrightarrow> X \<subseteq> Y"
by (metis Abs_Set_inverse CollectI set_predicate_def subclass'_def universe)

lemma subclassI: "(\<And>x. x \<in> X \<Longrightarrow> x \<in> Y) \<Longrightarrow> X \<subseteq> Y" 
using subclass'_def by blast

lemma subset: "(\<forall>x::Set. x \<in> X \<longrightarrow> x \<in> Y) \<longleftrightarrow> X \<subseteq> Y"
using subsetI subclass'_def by blast 


text{* The empty class is unique. *}

lemma empty_is_unique: "\<lbrakk>\<forall>y. y \<notin> x\<rbrakk> \<Longrightarrow> x = \<emptyset>" 
using empty_set extensionality by blast

text{* Lemmas/proving rules about singletons. *}

lemma singletonE: "x \<in> {y} \<Longrightarrow> x = y"
  using pairing by simp

lemma singletonE2: "x \<in> {x}"
  using pairing by simp

lemma singletonI: "\<forall>x. x \<in> {y} \<longleftrightarrow> x = y"
  using pairing by simp

lemma subset_of_singleton:  
    fixes b c
  assumes "b \<subseteq> {c}"
    shows "b=\<emptyset> \<or> b={c}"
proof -
  {assume "b \<noteq> \<emptyset>"
   then obtain d where "d\<in>b" by (metis empty_is_unique) 
   hence "d\<in>{c}"using assms using subclass'_def by blast 
   hence "d=c" using singletonE by blast
   hence "b={c}" by (metis \<open>d\<in>b\<close> assms equalityI pairing subsetI)}
  thus ?thesis by auto
qed

end