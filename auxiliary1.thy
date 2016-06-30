theory auxiliary1
imports axioms_class_existence
begin

text{* Lemmas about unions, complements, and intersections. *}

lemma unionI1: "x \<in> X \<Longrightarrow> x \<in> X \<union> Y"
  by (metis Abs_Set_inverse CollectI Ex4_9_a set_predicate_def universe)

lemma Co_Eq: "\<lbrakk>\<And>x :: Set. x \<in> A \<longleftrightarrow> x \<notin> B\<rbrakk> \<Longrightarrow> A = Co(B)"
using set_extensionality B3 by blast

lemma V_Co_Empty: "\<V> = Co(\<emptyset>)"
using Ex4_9_b empty_set Co_Eq by simp

lemma notin_inter_mono: "x \<notin> X \<Longrightarrow> x \<notin> X \<inter> Y"
proof (cases "set(x)")
  assume "set(x)"
  assume "x \<notin> X"
  then have "\<not>(x \<in> X \<and> x \<in> Y)" by simp
  with B2 set_extensionality `set(x)` show "x \<notin> X \<inter> Y" by (metis Abs_Set_inverse CollectI universe)
  next
  assume "\<not> set x"
  show "x \<notin> X \<inter> Y"
  proof
    assume "x \<in> X \<inter> Y"
    then have "set x" using set_predicate_def by auto
    with `\<not> set x` show "False" ..
  qed
qed

lemma union_iff_or: "x \<in> X \<union> Y \<longleftrightarrow> x \<in> X \<or> x \<in> Y" 
  by (metis Ex4_9_a Rep_Set_cases mem_Collect_eq set_predicate_def universe)


end