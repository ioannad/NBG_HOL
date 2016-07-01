theory axioms_class_existence
imports ntuples
begin

section{* Axioms of Class Existence *}

text{* Mendelson introduces seven ``Axioms of Class Existence''
       instead of the axiom schema of separation for classes. 
       We shall first introduce these axioms and then prove 
       that for any first order formula with one free variable, 
       whose bounded quantifiers are about sets, the following 
       axioms provide us with a class that contains exactly those
       sets that satisfy this formula for any class parameter that
       occurs in the formula. Before we give the Axioms of Class
       existence, we need to be able to talk about triples, apart
       from tuples. *}

axiomatization
  intersection :: "Class \<Rightarrow> Class \<Rightarrow> Class" (infixl "\<inter>" 80)
and
  complement :: "Class \<Rightarrow> Class" ("Co")
and
  domain :: "Class \<Rightarrow> Class" ("dom")
  where 
    B1: "\<exists>X::Class. \<forall>u v::Set. ((\<langle>u, v\<rangle> \<in> X) \<longleftrightarrow> u \<in> v)" 
      --"belongs-relation"
and B2: "\<forall>u::Set. (u \<in> (X\<inter>Y) \<longleftrightarrow> u\<in>X \<and> u\<in>Y)"
      -- "intersection"
and B3: "\<forall>u::Set. (u \<in> Co(X) \<longleftrightarrow> u \<notin> X)"
      -- "complement"
and B4: "\<forall>u::Set. (u \<in> dom(X)\<longleftrightarrow>(\<exists>v::Set. (\<langle>u, v\<rangle>\<in>X)))"
      -- "domain"
and B5: "\<exists>Z::Class. \<forall>u v::Set.(\<langle>u, v\<rangle>\<in>Z\<longleftrightarrow>u\<in>X)" 
      -- "projection to the first coordinate"
and B6: "\<exists>Z::Class. \<forall>u v w::Set. (\<langle>u, v, w\<rangle>\<in>Z \<longleftrightarrow> \<langle>v, w, u\<rangle>\<in>X)"
      -- "permutation of coordinates, all move 'to the left'"
and B7: "\<exists>Z::Class. \<forall>u v w::Set. (\<langle>u, v, w\<rangle>\<in>Z \<longleftrightarrow> \<langle>u, w, v\<rangle>\<in>X)"
      -- "permutation of the last two coordinates"

(* page 231 *)

(* The following are the uniqueness lemmas mentioned in the comments in the 
           beginning of page 231. *)

lemma intersection_unique: "\<exists>! Z :: Class. \<forall> u :: Set. (u\<in>Z \<longleftrightarrow> (u\<in>X \<and> u\<in>Y))"
unfolding Ex1_def 
proof (rule exI, rule conjI)
  def Z \<equiv> "X\<inter>Y"
  show "(\<forall>u::Set. u \<in> Z \<longleftrightarrow> (u \<in> X \<and> u \<in> Y))" using B2 Z_def by simp
  thus "(\<forall>Z'. (\<forall>u::Set. u \<in> Z' \<longleftrightarrow> (u \<in> X \<and> u \<in> Y)) \<longrightarrow> (Z' = Z)) "
    by (simp add: set_extensionality) 
qed

(* Same proof below! *)

lemma complement_unique: "\<exists>! Z :: Class. \<forall> u :: Set. (u\<in>Z \<longleftrightarrow> u\<notin>X)" 
unfolding Ex1_def 
proof (rule exI, rule conjI)
  def Z \<equiv> "Co X"
  show "(\<forall>u::Set. u \<in> Z \<longleftrightarrow> (u \<notin> X))" using B3 Z_def by simp
  thus "(\<forall>Z'. (\<forall>u::Set. u \<in> Z' \<longleftrightarrow> (u \<notin> X)) \<longrightarrow> (Z' = Z)) "
    by (simp add: set_extensionality) 
qed

(* And again "same". *)

text{* \textbf{FOMUS workshop exercise:} *}

lemma domain_unique: "\<exists>!Z::Class. \<forall>u::Set. (u\<in>Z \<longleftrightarrow> (\<exists>v::Set. (\<langle>u,v\<rangle>\<in>X)))"
sorry

abbreviation union :: "Class \<Rightarrow> Class \<Rightarrow> Class" (infixl "\<union>" 80) 
where "X\<union>Y \<equiv> Co( Co(X) \<inter> Co(Y) )"

abbreviation Class_difference :: "Class \<Rightarrow> Class \<Rightarrow> Class" 
  (infixl "\<setminus>" 80) 
where "X\<setminus>Y \<equiv> X \<inter> (Co(Y))"

text{* The last abbreviation in Mendelson's list of page 231 
       is one for the universal set. We have this already so we 
       prove the following lemma instead. *}

text{* The following is Exercise 4.9 in Mendelson. *}

lemma Ex4_9_a: "\<forall>u :: Set. u \<in> X \<union> Y \<longleftrightarrow> u \<in> X \<or> u \<in> Y"
  by (simp add: B2 B3)

lemma Ex4_9_b: "\<forall>u :: Set. u \<in> \<V>"
  by (metis Quotient_Set Quotient_rep_reflp Quotient_to_Domainp Set.domain_eq Set.pcr_cr_eq)

lemma Ex4_9_c: "\<forall>u::Set. u \<in> X \<setminus> Y \<longleftrightarrow> u \<in> X \<and> u \<notin> Y"
  by (simp add: B2 B3)

lemma Ex4_10_a: "X \<inter> Y = Y \<inter> X"
using Ex4_2 B2 by auto

lemma Ex4_10_b: "X \<union> Y = Y \<union> X"
using Ex4_2 B2 B3 by auto

lemma Ex4_10_c: "X \<subseteq> Y \<longleftrightarrow> (X \<inter> Y = X)"
proof
  assume "X \<subseteq> Y"
  with subclass'_def B2 Ex4_2 show "X \<inter> Y = X" by auto
  next
  assume assm: "X \<inter> Y = X"
  have "\<forall>Z. (Z \<in> X \<longrightarrow> Z \<in> Y)"
  proof
    fix Z
    show "Z \<in> X \<longrightarrow> Z \<in> Y"
    proof (rule ccontr, simp)
      assume assm2: "Z \<in> X \<and> Z \<notin> Y"
      then have "Z \<notin> Y" ..
      with assm B2 have "Z \<notin> X" by (metis Abs_Set_inverse Ex4_1 mem_Collect_eq universe) 
      with assm2 show "False" by simp
    qed
  qed
  with subclass'_def show "X \<subseteq> Y" by auto
qed


lemma Ex4_10_d: "X \<subseteq> Y \<longleftrightarrow> (X \<union> Y = Y)"
proof
  show "X \<subseteq> Y \<Longrightarrow> X \<union> Y = Y" using Ex4_2 B2 B3 subclass'_def by auto
  next  
  assume assm: "X \<union> Y = Y"
  have "\<forall>Z \<in> X. (Z \<in> Y)" unfolding forall_in_def
  proof
    fix Z::Set
    show "Z \<in> X \<longrightarrow> Z \<in> Y" 
    proof (rule ccontr, simp)
      assume assm1: "Z \<in> X \<and> Z \<notin> Y"
      then have "Z \<notin> Y" ..
      with assm have "Z \<notin> X \<union> Y" by simp
      then have "Z \<notin> X" using Ex4_9_a by blast 
      with assm1 show "False" by simp
    qed
  qed
  with subclass'_def forall_in_def  show "X \<subseteq> Y" by (metis Abs_Set_inverse CollectI Ex4_1 universe)
qed

lemma Ex4_10_e: "(X \<inter> Y) \<inter> Z = X \<inter> (Y \<inter> Z)"
using Ex4_2 B2 by auto

lemma Ex4_10_f: "(X \<union> Y) \<union> Z = X \<union> (Y \<union> Z)"
using Ex4_2 B2 B3 by auto

lemma Ex4_10_g: "X \<inter> X = X"
using Ex4_2 B2 by auto

lemma Ex4_10_h: "X \<union> X = X"
using Ex4_2 B2 B3 by auto

lemma Ex4_10_i: "X \<inter> \<emptyset> = \<emptyset>"
using Ex4_2 empty_set B2 by auto

lemma Ex4_10_j: "X \<union> \<emptyset> = X"
using Ex4_2 empty_set B2 B3 by auto

lemma Ex4_10_k: "X \<inter> \<V> = X" 
proof -
  have "\<forall>x::Set. x \<in> X \<inter> \<V> \<longleftrightarrow> x \<in> X"
  proof
    fix x
    show "x \<in> X \<inter> \<V> = x \<in> X"
    proof
      assume "x \<in> X \<inter> \<V>"
      with B2 show "x \<in> X" using Ex4_1 Ex4_10_c subclass'_def universe by metis
      next
      show "x \<in> X \<Longrightarrow> x \<in> X \<inter> \<V>" using Ex4_1 Ex4_10_c subclass'_def universe by metis 
    qed
  qed
  then show "X \<inter> \<V> = X" using Ex4_2 by simp
qed

lemma Ex4_10_l: "X \<union> \<V> = \<V>"
using Ex4_10_h Ex4_10_i by (metis Ex4_10_a Ex4_10_j Ex4_10_k) 

lemma Ex4_10_m: "Co(X \<union> Y) = Co(X) \<inter> Co(Y)"
using Ex4_10_g Ex4_10_h by auto

lemma Ex4_10_n: "Co(X \<inter> Y) = Co(X) \<union> Co(Y)"
using Ex4_10_g Ex4_10_h by auto

lemma Ex4_10_o: "X\<setminus>X = \<emptyset>" 
using B2 B3 Ex4_2 empty_set by auto

lemma Ex4_10_p: "\<V>\<setminus>X = Co(X)"
using Ex4_10_k Ex4_10_a by metis

lemma Ex4_10_q: "X \<setminus> (X \<setminus> Y) = X \<inter> Y"
proof -
  from B2 have "\<forall>x::Set. x \<in> X \<inter> (Co(X \<inter> Co(Y))) \<longleftrightarrow> x \<in> X \<and> x \<in> Co(X \<inter> Co(Y))" by simp
  with B3 have "\<forall>x::Set. x \<in> X \<inter> (Co(X \<inter> Co(Y))) \<longleftrightarrow> x \<in> X \<and> x \<notin> (X \<inter> Co(Y))" by simp
  with B2 have "\<forall>x::Set. x \<in> X \<inter> (Co(X \<inter> Co(Y))) \<longleftrightarrow> x \<in> X \<and> x \<notin> Co(Y)" by auto
  with B3 have "\<forall>x::Set. x \<in> X \<inter> (Co(X \<inter> Co(Y))) \<longleftrightarrow> x \<in> X \<and> x \<in> Y" by simp
  with B2 have "\<forall>x::Set. x \<in> X \<inter> (Co(X \<inter> Co(Y))) \<longleftrightarrow> x \<in> X \<inter> Y" by simp
  then show "X \<inter> (Co(X \<inter> Co(Y))) = X \<inter> Y" using Ex4_2 by simp
qed

lemma Ex4_10_r: "Y \<subseteq> Co(X) \<longrightarrow> X \<setminus> Y = X" by (metis Ex4_10_a Ex4_10_d Ex4_10_g Ex4_10_h)

lemma Ex4_10_s: "Co(Co(X)) = X" using Ex4_10_g Ex4_10_h by auto

lemma Ex4_10_t: "Co(\<V>) = \<emptyset>" by (metis Ex4_10_o Ex4_10_p) 


lemma Ex4_10_u: "X \<inter> (Y \<union> Z) = (X \<inter> Y) \<union> (X \<inter> Z)"
using B2 B3 Ex4_2 Ex4_9_a by auto 

lemma Ex4_10_v: "X \<union> (Y \<inter> Z) = (X \<union> Y) \<inter> (X \<union> Z)"
using B2 B3 Ex4_9_a Ex4_2  by auto



text{* Exercise 4.11. *}

lemma Ex_4_11_a: "\<forall>X. \<exists>Z. \<forall>u v. \<langle>u, v\<rangle> \<in> Z \<longleftrightarrow> \<langle>v, u\<rangle> \<in> X"
proof
  fix X
  obtain C where "\<forall>u v w. \<langle>v, u, w\<rangle> \<in> C \<longleftrightarrow> \<langle>v, u\<rangle> \<in> X" using B5 by blast
  moreover obtain D where "\<forall>u v w. \<langle>v, w, u\<rangle> \<in> D \<longleftrightarrow> \<langle>v, u, w\<rangle> \<in> C" using B7 by blast
  moreover obtain E where "\<forall>u v w. \<langle>u, v, w\<rangle> \<in> E \<longleftrightarrow> \<langle>v, w, u\<rangle> \<in> D" using B6 by blast
  ultimately have "\<forall>u v. \<langle>u, v\<rangle> \<in> dom(E) \<longleftrightarrow> \<langle>v, u\<rangle> \<in> X" using B4 by simp
  thus "\<exists>Z. \<forall>u v. \<langle>u, v\<rangle> \<in> Z \<longleftrightarrow> \<langle>v, u\<rangle> \<in> X" ..
qed

lemma Ex_4_11_b: "\<forall>X. \<exists>Z. \<forall>u v w. \<langle>u, v, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>u, w\<rangle> \<in> X"
proof
  fix X
  obtain C where "\<forall>u v w. \<langle>u, w, v\<rangle> \<in> C \<longleftrightarrow> \<langle>u, w\<rangle> \<in> X" using B5 by blast
  moreover obtain D where "\<forall>u v w. \<langle>u, v, w\<rangle> \<in> D \<longleftrightarrow> \<langle>u, w, v\<rangle> \<in> C" using B7 by blast
  ultimately show "\<exists>Z. \<forall>u v w. \<langle>u, v, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>u, w\<rangle> \<in> X" by blast
qed

lemma Ex_4_11_c: "\<forall>X. \<exists>Z. \<forall>v. \<forall>i :: nat \<Rightarrow> Set. \<langle>\<dots>, i(n), v\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, i(n)\<rangle> \<in> X"
using B5 by blast

(* page 232 *)

lemma Ex_4_11_d: "\<forall>X. \<exists>Z. \<forall>i :: nat \<Rightarrow> Set. ( \<langle>\<dots>,i(n + k)\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>,i(n)\<rangle> \<in> X)"
proof (induction k, simp_all, blast)
  fix k::nat 
  assume IH:  "\<forall>X. \<exists>Z. \<forall>i. (\<langle>\<dots>, i(n + k)\<rangle>) \<in> Z \<longleftrightarrow> \<langle>\<dots>, i(n)\<rangle> \<in> X"
  show "\<forall>X. \<exists>Z. \<forall>i. \<langle>\<dots>, i(n + k), i(Suc (n + k))\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, i(n)\<rangle> \<in> X"
  proof (rule allI)
    fix X::Class
    obtain C where C_def: "\<forall>i. \<langle>\<dots>, i(n + k)\<rangle> \<in> C \<longleftrightarrow> \<langle>\<dots>, i(n)\<rangle> \<in> X" using IH by blast
    obtain D where "\<forall>v. \<forall>i. \<langle>\<dots>, i(n + k), v\<rangle> \<in> D \<longleftrightarrow> \<langle>\<dots>, i(n + k)\<rangle> \<in> C"
      using Ex_4_11_c by blast
    hence "\<forall>i. \<langle>\<dots>, i(Suc (n + k))\<rangle> \<in> D \<longleftrightarrow> \<langle>\<dots>, i(n + k)\<rangle> \<in> C" using Tuple_All by simp
    thus "\<exists>Z. \<forall>i. \<langle>\<dots>, i(n + k), i(Suc (n + k))\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, i(n)\<rangle> \<in> X" 
      using C_def by auto
  qed
qed

lemma Ex4_11_e: "\<forall>X. \<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. (\<langle>\<dots>, x(k + m), xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k), xn\<rangle> \<in> X)"
proof (induct m)
  show "\<forall>X. \<exists>Z. \<forall>x xn. \<langle>\<dots>,x(k + 0), xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>,x(k), xn\<rangle> \<in> X" by auto
  fix m 
  assume "\<forall>X. \<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<langle>\<dots>, x(k + m), xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k), xn\<rangle> \<in> X"
  thus "\<forall>X. \<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<langle>\<dots>, x(k + Suc m), xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k), xn\<rangle> \<in> X" 
  proof -
    fix m::nat
    assume IA: "\<forall>X. \<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<langle>\<dots>, x(k + m), xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k), xn\<rangle> \<in> X"
    show "\<forall>X. \<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<langle>\<dots>, x(k + Suc m), xn\<rangle> \<in> Z  \<longleftrightarrow> \<langle>\<dots>, x(k), xn\<rangle> \<in> X"
    proof 
      fix X
      have "\<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<forall>v. (\<langle>\<dots>, x(k+m), v, xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k+m), xn\<rangle> \<in> X)" 
        using Ex_4_11_b by blast
      then obtain Z1 where "\<forall>x. \<forall>xn. \<forall>v.   (\<langle>\<dots>, x(k+m), v, xn\<rangle> \<in> Z1 \<longleftrightarrow> \<langle>\<dots>, x(k+m), xn\<rangle> \<in> X)" 
        by blast
      from IA have "\<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<langle>\<dots>, x(k+m), xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k),xn\<rangle> \<in> X"
        by blast
      then obtain Z2 where z2: "\<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<langle>\<dots>, x(k+m), xn\<rangle> \<in> Z2 \<longleftrightarrow> \<langle>\<dots>, x(k), xn\<rangle> \<in> X" 
        by blast
      have "\<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<forall>v. (\<langle>\<dots>, x(k+m), v, xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k+m), xn\<rangle> \<in> Z2)" 
        using Ex_4_11_b by blast
      hence *: "\<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<forall>v. (\<langle>\<dots>, x(k+m), v, xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k), xn\<rangle> \<in> X)" 
        using z2 by blast
      then obtain Z where z_def: "\<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<forall>v. 
        (\<langle>\<dots>, x(k+m), v, xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>,x(k), xn\<rangle> \<in> X)" by blast
      have #: "\<forall>Z. \<forall>xn::Set. \<forall>x::nat\<Rightarrow>Set. \<exists>v. 
        (\<langle>\<dots>, x(k + Suc m), xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k+m), v, xn\<rangle> \<in> Z)" by auto
      then have "\<forall>xn::Set. \<forall>x::nat\<Rightarrow>Set. (\<langle>\<dots>, x(k + Suc m), xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k), xn\<rangle> \<in> X)"
        using z_def by blast
      then show "\<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<forall>xn::Set. \<langle>\<dots>, x(k + Suc m), xn\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<dots>, x(k), xn\<rangle> \<in> X"
        by auto
    qed
  qed
qed

lemma Ex_4_11_f: "\<forall>X. \<exists>Z. \<forall>x. \<forall>v :: nat \<Rightarrow> Set. \<langle>\<dots>, v(m), x\<rangle> \<in> Z \<longleftrightarrow> x \<in> X"
proof
  fix X
  obtain C where "\<forall>u x. \<langle>x, u\<rangle> \<in> C \<longleftrightarrow> x \<in> X" using B5 by blast
  then obtain D where "\<forall>u x. \<langle>u, x\<rangle> \<in> D \<longleftrightarrow> x \<in> X" using Ex_4_11_a by fast
  then show "\<exists>Z. \<forall>x. \<forall>v :: nat \<Rightarrow> Set. \<langle>\<dots>, v(m), x\<rangle> \<in> Z \<longleftrightarrow> x \<in> X" by blast
qed


lemma Ex4_11_g: "\<forall>X. \<exists>Z. \<forall>x::nat\<Rightarrow>Set. \<langle>\<dots>, x(n)\<rangle> \<in> Z \<longleftrightarrow> (\<exists>y::Set. \<langle>\<dots>, x(n), y\<rangle> \<in> X)"
using B4 by blast


text{* \textbf{FOMUS workshop extra exercise:} *}

lemma Ex4_11_h: "\<forall>X. \<exists>Z. \<forall>u v w::Set. (\<langle>v, u, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>u, w\<rangle> \<in> X)"
sorry

lemma Ex4_11_i: "\<forall>X. \<exists>Z. \<forall>v::nat\<Rightarrow>Set. \<forall>u w::Set. \<langle>\<dots>, v(n), u, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>u, w\<rangle> \<in> X"
using Ex4_11_h by blast

end