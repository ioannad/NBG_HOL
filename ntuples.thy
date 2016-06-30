theory ntuples
imports axioms_base
begin

text{* First we define ordered pairs, and then n-tuples, before we prove the fundamental property
       of the ordered pair. *}

definition ordered_pair :: "Set \<Rightarrow> Set \<Rightarrow> Set"  
where "ordered_pair x y \<equiv> {{x}, {x,y}}"


text{* Here we formalise n-tuples, as a subtype of Set. *}

(* Taken from Product_Type.thy, lines 300-320*)
nonterminal ntuple_args
syntax
  "_ntuple"      :: "ntuple_args \<Rightarrow> Set \<Rightarrow> Set"        ("(1'\<langle>_,/ _'\<rangle>)")
  "_ntuple_arg"  :: "Set \<Rightarrow> ntuple_args"                   ("_")
  "_ntuple_args" :: "ntuple_args \<Rightarrow> Set \<Rightarrow> ntuple_args"     ("_,/ _")

translations
  "\<langle>x, y\<rangle>" \<rightleftharpoons> "CONST ordered_pair x y"
  "_ntuple (_ntuple_args y z) x" \<rightleftharpoons> "_ntuple (_ntuple_arg (_ntuple y z)) x"
(*  "_abs (\<langle>x,y\<rangle>) t" \<rightharpoonup> "\<lambda>(x, y). t"   *) (*not sure where it's useful*)

value "\<langle>x,y,z,r,h\<rangle>" 


text{* The fundamental property of ordered pairs. *}

lemma Prop4_3: "\<forall> x y u v :: Set. (\<langle>x,y\<rangle> = \<langle>u,v\<rangle>) \<longrightarrow> ((x=u) \<and> (y=v))" 

(* page 230 *)

proof (rule allI, rule allI, rule allI, rule allI, rule impI)
  fix x y u v :: Set   
  assume "\<langle>x,y\<rangle> = \<langle>u,v\<rangle>"                                     -- "Assume (x,y) = (u,v)." 
  then have 0: "{{x},{x,y}} = {{u},{u,v}}"                  -- "Then {{x},{x,y}} = {{u},{u,v}}."
    using ordered_pair_def by simp
  moreover have "{x} \<in> {{x}, {x,y}}" using pairing by auto  -- " Since {x} E {{x}, {x,y}},"
  ultimately have "{x} \<in> {{u}, {u, v}}"                     -- "{x} E {{u}, {u, v}}." 
    by auto
  moreover hence "{x} = {u} \<or> {x} = {u,v}" using pairing
    by (simp add: Rep_Set_inject)                           -- "Hence, {x} = {u} or {x} = {u,v}."
  moreover hence "x=u" by (metis Rep_Set_inject pairing)    -- "In either case x=u."
  moreover have *: "{u,v} \<in> {{u},{u,v}}" using pairing by simp -- "Now, {u,v} E {{u},{u,v}};" 
  moreover hence "{u,v} \<in> {{x},{x,y}}" using 0 by simp      -- "so, {u,v} E {{x},{x,y}}."
  moreover then have 2:"{u,v} = {x} \<or> {u, v} = {x,y}" by (simp add: Rep_Set_inject pairing)
                                                            -- "Then {u,v} = {x} or {u, v} = {x,y}."
  moreover have **: "{x,y} = {u} \<or> {x,y} = {u, v}" by (metis 0 Rep_Set_inverse pairing) 
                                                            -- "Similarly, {x,y} = {u} or {x,y} = {u, v}."
  moreover hence "y=v" 
(* Sledgehammer can find a proof from this poing already:
                           by (metis Rep_Set_inverse calculation(3) calculation(6) pairing)  *)
    proof (cases "{u,v} = {x} \<and> {x,y} = {u}")
      assume "{u,v} = {x} \<and> {x,y} = {u}"                    -- "If {u, v} = {x} and {x,y} = {u},"
      then have "x = y" by (metis Rep_Set_inverse pairing)
      moreover have "\<dots> = u" using \<open>x = u\<close> calculation by blast  
      moreover have "\<dots> = v" by (metis Rep_Set_inverse \<open>{u, v} = {x} \<and> {x, y} = {u}\<close> pairing)
                                                              -- " then x = y = u = v;"
      thus ?thesis by (metis Rep_Set_inject \<open>{u, v} = { x} \<and> {x, y} = { u}\<close> pairing) 
      next
      assume *: "\<not>({u,v} = {x} \<and> {x,y} = {u})"               -- " if not,"
      then have "{u, v} = {x,y}" using calculation(6) calculation(7) by auto 
                                                              -- "{u, v} = {x,y}."
      hence "{u, v} = {u, y}"  by (simp add: calculation(3))  --"Hence, {u, v} = {u, y}."
      show "y=v" 
      proof (cases "v\<noteq>u")
        assume "v\<noteq>u" thus "y=v" by (metis Rep_Set_inverse \<open>{u, v} = {u, y}\<close> pairing)
                                                              --"So, if v \<noteq> u, then y = v;"
        next 
        assume "\<not>(v\<noteq>u)" then have "y=u" using * \<open>{u, v} = {x, y}\<close> calculation(3) by auto
                                                              -- "if v = u, then y = v."
        thus "y=v" using \<open>\<not> v \<noteq> u\<close> by blast                  --"Thus, in all cases, y = v."
      qed
    qed 
  ultimately show "x = u \<and> y = v" by simp
qed

text{* The following exercises show that it doesn't matter how we define ordered pairs, as long
       as their fundamental property holds. *} 


text{* \textbf{FOMUS workshop extra exercise:} *}

lemma Ex4_8_a:    fixes op :: "Class \<Rightarrow> Class \<Rightarrow> Class" ("(\<lceil>_ , _\<rceil>)")
  assumes "\<lceil>X,Y\<rceil> = { {\<emptyset>,X} , {{\<emptyset>,Y}} } "
    shows "\<forall> x y u v :: Set. (\<lceil>x,y\<rceil> = \<lceil>u,v\<rceil>) \<longrightarrow> ((x=u) \<and> (y=v))"
oops


text{* \textbf{FOMUS workshop extra exercise:} *}

lemma Ex4_8_b:
  fixes op :: "Class \<Rightarrow> Class \<Rightarrow> Class" ("(\<lceil>_ , _\<rceil>)")
  assumes "\<lceil>X,Y\<rceil> = { {\<emptyset>,{X}} , {{Y}} } "
    shows "\<forall> x y u v :: Set. (\<lceil>x,y\<rceil> = \<lceil>u,v\<rceil>) \<longrightarrow> ((x=u) \<and> (y=v))"
oops



(* The following contains ToTuple and the relevant lemmas from FOL_Formula. 
   TO-DO: define the notation "\<langle>x_1,\<dots>,x_n\<rangle>" *)
 
text {* Sometimes we need to use metafunctions of type nat \<Rightarrow> Set to describe tuples. 
        \texttt{ToTuple} takes an interpretation \tt{i::nat$\Rightarrow$Set} and an 
        Isabelle-natural number \tt{n::nat} and returns the tuple 
        \tt{$\langle i(0), \dots, i(n)\rangle$}
        In this way we can refer to arbitrary n-tuples. *}

primrec ToTuple :: "[nat \<Rightarrow> Set, nat] \<Rightarrow> Set"
where 
  "ToTuple i 0 = i(0)"
  | "ToTuple i (Suc n) = \<langle>ToTuple i n, i(Suc n)\<rangle>"
-- "We sometimes call (ToTuple i n) the (n+1)-tuple coming from i."
notation ToTuple ("(\<langle>\<dots>,(1_)((2_))\<rangle>)")  
(* For now, I don't know how to refer to an argument twice in a notation. It should be:
   \<langle> (1_)(0),...,(1_)((2_))\<rangle>. *)

abbreviation ToTuple_add1 :: "(nat\<Rightarrow>Set) \<Rightarrow> nat \<Rightarrow> Set \<Rightarrow> Set" ("(\<langle>\<dots>, _ (_), _\<rangle>)")  
where "\<langle>\<dots>,i(n),x\<rangle> \<equiv> \<langle> \<langle>\<dots>,i(n)\<rangle>,x\<rangle>"

abbreviation ToTuple_add2 :: "(nat\<Rightarrow>Set) \<Rightarrow> nat \<Rightarrow> Set \<Rightarrow> Set \<Rightarrow> Set" ("(\<langle>\<dots>,_ (_), _, _\<rangle>)")  
where "\<langle>\<dots>,i(n),x,y\<rangle> \<equiv> \<langle> \<langle>\<dots>,i(n)\<rangle>,x,y\<rangle>"

text {* Some basic lemmas about n-tuples. *}

lemma Tuple_Eq: "\<langle>\<dots>,i(n)\<rangle> = \<langle>\<dots>,j(n)\<rangle> \<Longrightarrow> \<forall>k \<le> n. i(k) = j(k)"
-- "Equal n-tuples from different interpretations imply that the interpretations are the same 
    below n."
proof (induct n, simp_all)
  fix n::nat
  assume IH:   "(\<langle>\<dots>,i(n)\<rangle> = \<langle>\<dots>,j(n)\<rangle> \<Longrightarrow> \<forall>k\<le>n. i(k) = j(k))" 
     and assm: "\<langle>\<dots>,i(n), i(Suc n)\<rangle> = \<langle>\<dots>, j(n), j(Suc n)\<rangle>"
  thus "\<forall>k\<le>Suc n. i k = j k" using Prop4_3 le_Suc_eq by blast
qed

lemma Tuple_Dom: "\<lbrakk>\<And>k. k \<le> n \<Longrightarrow> x(k) = y(k)\<rbrakk> \<Longrightarrow> \<langle>\<dots>,x(n)\<rangle> = \<langle>\<dots>,y(n)\<rangle>"
-- "If two interpretations are the same below n, then they produce the same n-tuples."
by (induct n, simp_all)

lemma Tuple_All1: "(\<forall>v. \<forall>i. \<phi>( \<langle>\<dots>, i(n), v\<rangle> )) \<Longrightarrow> (\<forall>i. \<phi>( \<langle>\<dots>,i(Suc n)\<rangle> ))"
-- "If \<phi> holds for every (n+2) tuple, whose first (n+1) elements may come from any i, then \<phi> holds 
    for the (n+2) tuple coming from any i."
by simp

lemma Tuple_All2: "(\<forall>i. \<phi>( \<langle>\<dots>, i(Suc n)\<rangle> )) \<Longrightarrow> (\<forall>v. \<forall>i. \<phi>(\<langle>\<dots>,i(n), v\<rangle>))"
-- "The reverse of Tuple_All1."
proof
  fix v
  assume A1: "\<forall>i. \<phi>( \<langle>\<dots>, i(Suc n)\<rangle> )"
  show "\<forall>i. \<phi>(\<langle>\<dots>,i(n), v\<rangle>)" 
  proof
    fix i :: "nat \<Rightarrow> Set"
    have "ToTuple (\<lambda>k. if k = (Suc n) then v else i(k)) (Suc n)
      = \<langle>ToTuple (\<lambda>k. if k = (Suc n) then v else i(k)) n, v\<rangle>" by simp
    also have "\<dots> = \<langle>\<dots>,i(n), v\<rangle>"
      using Tuple_Dom [of n i "\<lambda>k. if k = (Suc n) then v else i(k)"] by simp
    finally show "\<phi>(\<langle>\<dots>, i(n), v\<rangle>)" using A1 by metis
  qed
qed

lemma Tuple_All: "(\<forall>i::nat\<Rightarrow>Set. \<phi>( \<langle>\<dots>, i(Suc n)\<rangle>)) \<longleftrightarrow> (\<forall>v::Set. \<forall>i::nat\<Rightarrow>Set. \<phi>(\<langle>\<dots>, i(n), v\<rangle>))"
using Tuple_All1 Tuple_All2 by auto




end
