theory ordinals
imports axioms_to_infinity
begin
section{* Ordinal Numbers *}

(* Ioanna: page 240, continued *)

definition Irrefl_rel_on:: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "Irr" 70)
where "X Irr Y \<longleftrightarrow> (Rel(X) \<and> (\<forall>y::Set. y \<in> Y \<longrightarrow> \<langle>y,y\<rangle> \<notin> X))"
notation Irrefl_rel_on ("(_ is an irreflexive relation on _)" 70)

definition Trans_rel_on:: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "Tr" 70)
where "X Tr Y \<longleftrightarrow> (Rel(X) \<and> (\<forall>u v w. (u \<in> Y \<and> v \<in> Y \<and> w \<in> Y \<and> \<langle>u,v\<rangle> \<in> X \<and> \<langle>v,w\<rangle> \<in> X) 
                   \<longrightarrow> \<langle>u,w\<rangle> \<in> X))"
notation Trans_rel_on ("(_ is a transitive relation on _)" 70)

definition Part_ord_on:: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "Part" 70)
where "X Part Y \<longleftrightarrow> (X Irr Y) \<and> (X Tr Y)"
notation Part_ord_on ("(_ partially orders _)" 70)

definition Conn_rel_on:: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "Con" 70)
where "X Con Y \<longleftrightarrow> Rel(X) \<and> (\<forall>u v.(u \<in> Y \<and> v \<in> Y \<and> u \<noteq> v) \<longrightarrow> (\<langle>u,v\<rangle> \<in> X \<or> \<langle>v,u\<rangle> \<in> X))"
notation Conn_rel_on ("(_ is a connected relation on _)" 70)

definition Tot_ord_on:: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "Tot" 70)
where "X Tot Y \<longleftrightarrow> (X Irr Y) \<and> (X Tr Y) \<and> (X Con Y)"
notation Tot_ord_on ("(_ totally orders _)" 70)

definition Well_ord_of:: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "We" 70)
where "X We Y \<longleftrightarrow> (X Irr Y) \<and> (\<forall>Z.(Z \<subseteq> Y \<and> Z \<noteq> Rep_Set \<emptyset>) \<longrightarrow> 
  (\<exists>y. y \<in> Z \<and> (\<forall>v. (v \<in> Z \<and> v \<noteq> y) \<longrightarrow> \<langle>y,v\<rangle> \<in> X \<and> \<langle>v,y\<rangle> \<notin> X)))"
notation Well_ord_of ("(_ is a well-ordering of _)" 70)
notation Well_ord_of ("(_ well-orders _)" 70)

(* Ioanna: page 241 *)

(* Ioanna: perhaps a proof of uniqueness is a good idea here. *)
abbreviation is_the_least_in_wrt:: "Set \<Rightarrow> Class \<Rightarrow> Class \<Rightarrow> bool" 
  ("(_ is the least in _ with respect to _)" 70)
  where "y is the least in Z with respect to X \<equiv> 
             (y \<in> Z \<and> (\<forall>v. (v \<in> Z \<and> v \<noteq> y) \<longrightarrow> \<langle>y,v\<rangle> \<in> X \<and> \<langle>v,y\<rangle> \<notin> X))"
notation is_the_least_in_wrt ("_ is the min(_) wrt. _" 70)

abbreviation has_least_element_wrt:: "Class \<Rightarrow> Class \<Rightarrow> bool" 
  ("(_ has a least element with respect to _)" 70)
  where "(Z has a least element with respect to X) \<equiv>
         (\<exists>y. (y is the least in Z with respect to X))"
notation has_least_element_wrt ("the min(_) wrt. _ exists" 70)


(* Perhaps it is a good idea here to add lemmas connecting this notion to total orders,
   wellorders, etc. *)

lemma Ex4_24: "X We Y \<longrightarrow> X Tot Y" 
(* [Hint: To show X Con Y, let x E Y 1\ y
E Y 1\ x =I- y. Then {x,y} has a least element, say x. Then (x,y) EX. To show
X Tr Y, assumex E Y 1\ y E Y 1\ z E Y 1\ (x,y) EX 1\ (y, z) EX. Then {x,y, z}
has a least element, which must be x.] *)
proof(unfold Tot_ord_on_def Well_ord_of_def, auto)
  assume 1: "X Irr Y" and 2: "\<forall>Z.((Z \<subseteq> Y \<and> Z \<noteq> Rep_Set \<emptyset>) \<longrightarrow> (\<exists>y. y \<in> Z \<and> (\<forall>v. (v \<in> Z \<and> v \<noteq> y) 
                                                                \<longrightarrow> \<langle>y,v\<rangle> \<in> X \<and> \<langle>v,y\<rangle> \<notin> X)))"
  {from this show "X Tr Y" 
  proof(unfold Trans_rel_on_def, auto)
    from 1 show "Rel X" by (simp add: Irrefl_rel_on_def)
    next fix u v w
    assume uY: "u \<in> Y" and vY: "v \<in> Y" and wY: "w \<in> Y" and "\<langle>u,v\<rangle> \<in> X" and "\<langle>v,w\<rangle> \<in> X"
    def T \<equiv> "{u,v}\<union>{w}"
    from this have "u \<in> T" and "v \<in> T" and "w \<in> T" by (simp add: union_iff_or T_def pairing)+
    have "T \<subseteq> Y"
    proof -
      {fix x
        assume "x \<in> T"
        from this have "x = u \<or> x = v \<or> x = w" by (simp add: union_iff_or T_def pairing)
        from this uY vY wY have "x \<in> Y" by blast}
      from this show "T \<subseteq> Y" by (simp add: subclass'_def)
    qed
    from T_def have "\<forall>x. x \<in> T \<longleftrightarrow> (x = u \<or> x = v \<or> x = w)" 
      by (simp add: union_iff_or T_def pairing) 
    from this empty_set have "T \<noteq> \<emptyset>" by blast
    from this \<open>T \<subseteq> Y\<close> have 3: "T \<subseteq> Y \<and> T \<noteq> \<emptyset>" by simp
    from 2 this have "\<exists>y. y \<in> T \<and> (\<forall>x. (x \<in> T \<and> x \<noteq> y) \<longrightarrow> \<langle>y,x\<rangle> \<in> X \<and> \<langle>x,y\<rangle> \<notin> X)" by simp
    from this obtain y where y1: "y \<in> T" and y2: "\<forall>x. (x \<in> T \<and> x \<noteq> y) \<longrightarrow> \<langle>y,x\<rangle> \<in> X \<and> \<langle>x,y\<rangle> \<notin> X" 
      by blast
    from \<open>y \<in> T\<close> have "y = u \<or> y = v \<or> y = w" by (simp add: Rep_Set_inject
      `\<forall>x. x \<in> T = (x = Rep_Set u \<or> x = Rep_Set v \<or> x = Rep_Set w)`)
    from this have "y = u"
      using `Rep_Set \<langle>u, v\<rangle> \<in> X` `Rep_Set \<langle>v, w\<rangle> \<in> X` `Rep_Set u \<in> T` `Rep_Set v \<in> T` y2 by blast
    from this y2 \<open>w \<in> T\<close> show "\<langle>u, w\<rangle> \<in> X" using `Rep_Set \<langle>v, w\<rangle> \<in> X` `Rep_Set v \<in> T` by blast
  qed}
  show "X Con Y"
  proof(unfold Conn_rel_on_def, auto)
    from 1 show "Rel X" by (simp add: Irrefl_rel_on_def)
    next fix u v
    assume "u \<in> Y" and "v \<in> Y" and "u \<noteq> v" and "\<langle>v, u\<rangle> \<notin> X"
    show "\<langle>u, v\<rangle> \<in> X"
    proof -
      def T \<equiv> "{u,v}"
      from this \<open>u \<in> Y\<close> \<open>v \<in> Y\<close> have "T \<subseteq> Y" using pairing subsetI by presburger 
      from this 2 T_def have "\<exists>y. y \<in> T \<and> (\<forall>v. (v \<in> T \<and> v \<noteq> y) \<longrightarrow> \<langle>y,v\<rangle> \<in> X \<and> \<langle>v,y\<rangle> \<notin> X)"
        by (metis empty_set pairing)
      from this obtain y where "y \<in> T" and "\<forall>v. (v \<in> T \<and> v \<noteq> y) \<longrightarrow> \<langle>y,v\<rangle> \<in> X \<and> \<langle>v,y\<rangle> \<notin> X" by blast
      from this \<open>\<langle>v, u\<rangle> \<notin> X\<close> show "\<langle>u, v\<rangle> \<in> X" by (metis Rep_Set_inverse T_def `u \<noteq> v` pairing)
    qed
  qed
qed

lemma Ex4_25: "X We Y \<and> Z \<subseteq> Y \<longrightarrow> X We Z"
proof(auto)
  assume 1: "X We Y" and 2: "Z \<subseteq> Y"
  from 1 have 3: "\<forall>Z.(Z \<subseteq> Y \<and> Z \<noteq> Rep_Set \<emptyset>) \<longrightarrow> (\<exists>y. y \<in> Z \<and> (\<forall>v. (v \<in> Z \<and> v \<noteq> y) 
                                              \<longrightarrow> \<langle>y,v\<rangle> \<in> X \<and> \<langle>v,y\<rangle> \<notin> X))"
    by (auto simp only: Well_ord_of_def)
  from 1 2 have fin1: "X Irr Z" by (meson Irrefl_rel_on_def Well_ord_of_def subset) 
  from 1 2 have fin2: "\<forall>W.(W \<subseteq> Z \<and> W \<noteq> Rep_Set \<emptyset>) \<longrightarrow>
    (\<exists>y. y \<in> W \<and> (\<forall>v. (v \<in> W \<and> v \<noteq> y) \<longrightarrow> \<langle>y,v\<rangle> \<in> X \<and> \<langle>v,y\<rangle> \<notin> X))"
  proof -
    {fix W
      assume "W \<subseteq> Z" and "W \<noteq> Rep_Set \<emptyset>"
      from this 2 subclass'_def have "W \<subseteq> Y" by auto
      from this \<open>W \<noteq> Rep_Set \<emptyset>\<close> 3 have "\<exists>y. y \<in> W \<and> (\<forall>v. (v \<in> W \<and> v \<noteq> y)  
                                                      \<longrightarrow> \<langle>y,v\<rangle> \<in> X \<and> \<langle>v,y\<rangle> \<notin> X)" by simp}
    from this show ?thesis by simp
  qed
  from fin1 fin2 show "X We Z" by (simp only: Well_ord_of_def)
qed

(* Ioanna: Here go Examples 1 - 3: 
           Examples (from intuitive set theory)
1. The relation < on the set P of positive integers well-orders P.
2. The relation< on the set of all integers totally orders, but does not wen-
order, this set. The set has no least element.
3. The relation c on the set W of all subsets of the set of integers partially
orders W but does not totally order W. For example, {1} \<cent>. {2} and
{2} \<cent>. {1}.
*)

definition Sim_map_on :: "Class \<Rightarrow> Class \<Rightarrow> Class \<Rightarrow> bool" ("Simp")
where "Simp Z W1 W2 \<longleftrightarrow> (\<exists>x1 x2 r1 r2:: Set. 
                          Rel(r1) 
                          \<and> Rel(r2) 
                          \<and> (W1 = Rep_Set \<langle>r1,x1\<rangle>) 
                          \<and> (W2 = Rep_Set \<langle>r2, x2\<rangle>)
                          \<and> (Z is an injection) 
                          \<and> (dom(Z) = x1) 
                          \<and> (ran(Z) = x2) 
                          \<and> (\<forall>u v. (u \<in> x1 \<and> v \<in> x1) \<longrightarrow> (\<langle>u,v\<rangle> \<in> r1 \<longleftrightarrow> \<langle>(Z\<acute>u),(Z\<acute>v)\<rangle> \<in> r2)))"
notation Sim_map_on ("(_ is a similarity mapping of _ onto _)" 70)

definition Sim_ord_str :: "Class \<Rightarrow> Class \<Rightarrow> bool" ("Sim")
where "Sim W1 W2 \<longleftrightarrow> (\<exists>z. Simp z W1 W2)"
notation Sim_ord_str ("(_ and _ are similar ordered structures)" 70)
notation Sim_ord_str ("(_ and _ are similar ordered)" 70)
notation Sim_ord_str ("(_ and _ are similar)" 70)
notation Sim_ord_str ("(_ is similar to _)" 70)

(* The following makes certain theorem statements nicer to word (e.g., Corollary 4.17
   on page 251).*)
abbreviation not_similar :: "Class \<Rightarrow> Class \<Rightarrow> bool" ("(_ and _ are not similar)" 70)
  where "X and Y are not similar \<equiv> \<not> (X and Y are similar)"

(* Ioanna: Here goes the example after the definition of similar ordered structures. *)
  
lemma composition_definable[defining]: 
"definable(\<lambda>x::Set. (\<exists>u v w. x = \<langle>u,v\<rangle> \<and> \<langle>u,w\<rangle> \<in> Y \<and> \<langle>w,v\<rangle> \<in> X))"
sorry 

definition composition :: "Class \<Rightarrow> Class \<Rightarrow> Class" (infixl "\<circ>" 80)
  where "X \<circ> Y = { x::Set \<bar> (\<exists>u v w. x = \<langle>u,v\<rangle> \<and> \<langle>u,w\<rangle> \<in> Y \<and> \<langle>w,v\<rangle> \<in> X)}"

lemma composition_lemma: "\<forall>x. x \<in> X \<circ> Y \<longleftrightarrow> (\<exists>u v w. x = \<langle>u,v\<rangle> \<and> \<langle>u,w\<rangle> \<in> Y \<and> \<langle>w,v\<rangle> \<in> X)"
sorry

(*Jakob: I added the following lemma to faciliate some proofs*)
lemma composition_lemma2: "\<langle>u,v\<rangle> \<in> X \<circ> Y \<longleftrightarrow> (\<exists>w. \<langle>u,w\<rangle> \<in> Y \<and> \<langle>w,v\<rangle> \<in> X)"
sorry

(* Ioanna: page 242 *)

lemma Ex4_26_a: "(Simp Z X Y) \<longrightarrow> set(Z) \<and> set(X) \<and> set(Y)"
proof auto
  assume 1: "Simp Z X Y"
  show "set(Z)" using Ex4_15_c Sim_map_on_def Cor4_6_b
  proof -
    from 1 have "\<exists>x::Set. dom(Z) = x" and "\<exists>y::Set. ran(Z) = y" and "Rel(Z)" using Fnc1_def Fnc_def
      by(auto simp: Sim_map_on_def)+
    from \<open>\<exists>x::Set. dom(Z) = x\<close> have "set(dom(Z))" using Ex4_9_b universe by auto
    from \<open>\<exists>y::Set. ran(Z) = y\<close> have "set(ran(Z))" using Ex4_9_b universe by auto
    from \<open>set(dom(Z))\<close> \<open>set(ran(Z))\<close> \<open>Rel(Z)\<close> show "set(Z)" using Ex4_15_c by blast
  qed
  show "set(X)"
  proof -
    from 1 have "\<exists>x y. X = \<langle>x,y\<rangle>" by(auto simp: Sim_map_on_def)
    from this show "set(X)" using Ex4_9_b universe by auto
  qed
  show "set(Y)"
  proof -
    from 1 have "\<exists>x y. Y = \<langle>x,y\<rangle>" by(auto simp: Sim_map_on_def)
    from this show "set(Y)" using Ex4_9_b universe by auto
  qed
qed

lemma Ex4_26_b: "(Simp Z X Y) \<longrightarrow> (Simp (Inv Z) Y X)" 
proof -
  {assume 1: "Simp Z X Y"
    from this have "Fnc1(Inv(Z))"
    proof -
      from 1 have "Fnc1(Z)" using Sim_map_on_def by auto
      from this have "Fnc(Z)" and "Fnc(Inv(Z))" by(simp only: Fnc1_def)+
      from this have "Inv(Inv(Z)) = Z \<inter> (\<V> \<times> \<V>)" by(simp add: square Ex4_12_o)
      have fin1: "Fnc(Inv(Inv(Z)))"
      proof (unfold Fnc_def, auto)
        from \<open>Inv(Inv(Z)) = Z \<inter> (\<V> \<times> \<V>)\<close> have "Inv(Inv(Z)) \<subseteq> \<V> \<times> \<V>" 
          using B2 subsetI by fastforce
        from this show "Rel(Inv(Inv(Z)))" by(simp only: square relation_predicate_def)
        next fix x y z
        assume "Rep_Set \<langle>x, y\<rangle> \<in> Inv (Inv Z)" and "Rep_Set \<langle>x, z\<rangle> \<in> Inv (Inv Z)"
        from \<open>Inv(Inv(Z)) = Z \<inter> (\<V> \<times> \<V>)\<close> this have "Rep_Set \<langle>x, y\<rangle> \<in> Z" and "Rep_Set \<langle>x, z\<rangle> \<in> Z"
          using notin_inter_mono by auto
        from this \<open>Fnc(Z)\<close> show "y = z" using Fnc_def by auto
      qed
      from this \<open>Fnc(Inv(Z))\<close> show "Fnc1(Inv(Z))" using Fnc1_def by simp
    qed
    from 1 obtain x1 x2 r1 r2 where 2: "Rel(r1) \<and> Rel(r2) \<and> (X = Rep_Set \<langle>r1,x1\<rangle>)
                     \<and> (Y = Rep_Set \<langle>r2, x2\<rangle>) \<and> Fnc1(Z) \<and> (dom(Z) = x1) \<and> (ran(Z) = x2)
                     \<and> (\<forall>u v. (u \<in> x1 \<and> v \<in> x1) \<longrightarrow> (\<langle>u,v\<rangle> \<in> r1 \<longleftrightarrow> \<langle>Z\<acute>u,Z\<acute>v\<rangle> \<in> r2))"
      using Sim_map_on_def by blast
    from this have fin2: "dom(Inv(Z)) = x2" sorry
    from 2 have fin3: "ran(Inv(Z)) = x1" sorry
    from 2 have "(\<forall>u v. (u \<in> x1 \<and> v \<in> x1) \<longrightarrow> (\<langle>(Inv(Z))\<acute>u,(Inv(Z))\<acute>v\<rangle> \<in> r1
                                                \<longleftrightarrow> \<langle>(Inv(Inv(Z)))\<acute>u,(Inv(Inv(Z)))\<acute>v\<rangle> \<in> r2))"
    sorry
    from this have "(Simp (Inv Z) Y X)" sorry}
  from this show ?thesis ..
oops

lemma Ex4_27_a: "Rel(X) \<and> Rel(Y) \<longrightarrow> Rel(X \<circ> Y)"
proof -
  {assume "Rel(X)" and "Rel(Y)"
    from this have "\<forall>x. x \<in> X \<circ> Y \<longrightarrow> (\<exists>u v w. x = \<langle>u,v\<rangle> \<and> \<langle>u,w\<rangle> \<in> Y \<and> \<langle>w,v\<rangle> \<in> X \<and> u \<in> \<V> \<and> v \<in> \<V>)"
      by (simp add: Ex4_9_b composition_lemma)}
  thus ?thesis using cartesian_product_lemma relation_predicate_def by (metis square subsetI)
qed

lemma Ex4_27_c: "(X is a function) \<and> (Y is a function) \<longrightarrow> ((X \<circ> Y) is a function)"
proof -
  {assume 1: "Fnc(X) \<and> Fnc(Y)"
    from this have "Rel(X \<circ> Y)" by (simp only: Fnc_def Ex4_27_a)
    {fix x y z::Set
      assume "\<langle>x,y\<rangle> \<in> (X \<circ> Y) \<and> \<langle>x,z\<rangle> \<in> (X \<circ> Y)"
      from this have "\<exists>v. \<langle>x,v\<rangle> \<in> Y \<and> \<langle>v,y\<rangle> \<in> X" and "\<exists>w. \<langle>x,w\<rangle> \<in> Y \<and> \<langle>w,z\<rangle> \<in> X"
        by(auto simp: composition_lemma2)
      from this obtain v w where 2: "\<langle>x,v\<rangle> \<in> Y \<and> \<langle>v,y\<rangle> \<in> X" and 3: "\<langle>x,w\<rangle> \<in> Y \<and> \<langle>w,z\<rangle> \<in> X" by blast
      from this 1 have "v = w" using Fnc_def by auto
      from this 1 2 3 have "y = z" using Fnc_def by auto}
    from this \<open>Rel(X \<circ> Y)\<close> have "Fnc(X \<circ> Y)" using Fnc_def by auto}
  from this show ?thesis ..
qed

lemma Ex4_27_d: "(X is an injection) \<and> (Y is an injection) \<longrightarrow> ((X \<circ> Y) is an injection)"
proof -
  {assume 1: "Fnc1(X) \<and> Fnc1(Y)"
    from this have fin1: "Fnc(X \<circ> Y)" using Fnc1_def Ex4_27_c by auto
    from 1 have fin2: "Fnc(Inv(X \<circ> Y))"
    proof(unfold Fnc_def, auto)
      show "Rel (Inv(X \<circ> Y))"
      proof -
        {fix x
          assume "x \<in> Inv(X \<circ> Y)"
          from this have "\<exists>u v. x = \<langle>u,v\<rangle> \<and> \<langle>v,u\<rangle> \<in> (X \<circ> Y)" sorry
          from this have "x \<in> \<V> \<times> \<V>" using Ex4_9_b cartesian_product_lemma by blast}
        from this show ?thesis using relation_predicate_def by (simp add: square subsetI)
      qed
      show "\<And>x y z. Rep_Set \<langle>x, y\<rangle> \<in> Inv (X \<circ> Y) \<Longrightarrow> Rep_Set \<langle>x, z\<rangle> \<in> Inv (X \<circ> Y) \<Longrightarrow> y = z"
      proof -
        {fix x y z
          assume "\<langle>x, y\<rangle> \<in> Inv (X \<circ> Y)" and "\<langle>x, z\<rangle> \<in> Inv (X \<circ> Y)"
          from this have "\<langle>y,x\<rangle> \<in> X \<circ> Y" and "\<langle>z,x\<rangle> \<in> X \<circ> Y" by(simp only: inverse_relation_lemma)+
          from this have "\<exists>v. \<langle>y,v\<rangle> \<in> Y \<and> \<langle>v,x\<rangle> \<in> X" and "\<exists>w. \<langle>z,w\<rangle> \<in> Y \<and> \<langle>w,x\<rangle> \<in> X"
            by(auto simp: composition_lemma2)
          from this obtain v w where 2: "\<langle>y,v\<rangle> \<in> Y \<and> \<langle>v,x\<rangle> \<in> X" and 3: "\<langle>z,w\<rangle> \<in> Y \<and> \<langle>w,x\<rangle> \<in> X" by blast
          from this have "v \<in> dom(X)" and "w \<in> dom(X)" using B4 by auto
          from 2 3 have "X\<acute>v = X\<acute>w" sorry
          from this 1 2 3 \<open>v \<in> dom(X)\<close> \<open>w \<in> dom(X)\<close> have "v = w" using Ex4_17_c Fnc1_def by blast
          from 2 3 have "y \<in> dom(Y)" and "z \<in> dom(Y)" using B4 by auto
          from \<open>v=w\<close> 2 3 have "Y\<acute>y = Y\<acute>z" sorry
          from this 1 2 3 \<open>y \<in> dom(Y)\<close> \<open>z \<in> dom(Y)\<close> have "y = z" using Ex4_17_c Fnc1_def by blast}
        from this show "\<And>x y z. Rep_Set \<langle>x, y\<rangle> \<in> Inv (X \<circ> Y) \<Longrightarrow> Rep_Set \<langle>x, z\<rangle> \<in> Inv (X \<circ> Y)
                          \<Longrightarrow> y = z" by blast
      qed
    qed
    from fin1 fin2 have "Fnc1(X \<circ> Y)" using Fnc1_def by simp}
  from this show ?thesis ..
oops 

lemma Ex4_27_e: "(X1: Z \<rightarrow> W) \<and> (X2: Y \<rightarrow> Z) \<longrightarrow> ((X1 \<circ> X2): Y \<rightarrow> W)"
proof(unfold function_from_to_def, auto)
  assume 1: "Fnc(X1)" and 2: "Z = dom(X1)" and 3: "ran X1 \<subseteq> W" and 4: "Fnc(X2)"
          and 5: "ran X2 \<subseteq> dom X1" and 6: "Y = dom X2"
  from 1 4 show "Fnc(X1 \<circ> X2)" using Ex4_27_c by simp
  show "dom (X1 \<circ> X2) = dom X2"
  proof -
    {fix x::Set
      assume "x \<in> dom(X2)"
      from this have "\<exists>u. \<langle>x,u\<rangle> \<in> X2" using B4 by auto
      from this obtain u where "\<langle>x,u\<rangle> \<in> X2" by blast
      from this have "u \<in> ran(X2)" using range_lemma by auto
      from this 5 have "u \<in> dom(X1)" using subset by blast
      from this have"\<exists>v. \<langle>u,v\<rangle> \<in> X1" using B4 by auto
      from this \<open>\<langle>x,u\<rangle> \<in> X2\<close> have "\<exists>v. \<langle>x,v\<rangle> \<in> X1 \<circ> X2" using composition_lemma2 by blast
      from this have "x \<in> dom(X1 \<circ> X2)" using B4 by auto}
    from this have fin1: "dom(X2) \<subseteq> dom(X1 \<circ> X2)" by (simp add: subsetI)
    {fix x::Set
      assume "x \<in> dom(X1 \<circ> X2)"
      from this have "\<exists>u. \<langle>x,u\<rangle> \<in> X1 \<circ> X2" using B4 by auto
      from this obtain u where "\<langle>x,u\<rangle> \<in> X1 \<circ> X2" by blast
      from this have "\<exists>w. \<langle>x,w\<rangle> \<in> X2 \<and> \<langle>w,u\<rangle> \<in> X1" using composition_lemma2 by simp
      from this have "x \<in> dom(X2)" using B4 by auto}
    from this have fin2: "dom(X1 \<circ> X2) \<subseteq> dom(X2)" by (simp add: subsetI)
    from fin1 fin2 show ?thesis using Prop4_1_a by auto
  qed
  show "ran(X1 \<circ> X2) \<subseteq> W"
  proof -
    {fix x::Set
      assume "x \<in> ran(X1 \<circ> X2)"
      from this have "\<exists>v::Set. \<langle>v,x\<rangle> \<in> X1 \<circ> X2" by(simp add: range_lemma)
      from this have "\<exists>v w::Set. \<langle>v,w\<rangle> \<in> X2 \<and> \<langle>w,x\<rangle> \<in> X1" using composition_lemma2 by auto
      from this have "x \<in> ran(X1)" by(auto simp: range_lemma)
      from this 3 have "x \<in> W" using subclass'_def by simp}
    from this show ?thesis using subset by auto
  qed
qed

definition field :: "Class \<Rightarrow> Class" ("Fld")
where "Fld(X) \<equiv> dom(X) \<union> ran(X)"
notation field ("(the field of _)" 70)

definition Tot_ord :: "Class \<Rightarrow> bool" ("TOR")
where "TOR(X) \<longleftrightarrow> Rel(X) \<and> (X Tot (Fld(X)))"
notation Tot_ord ("(_ is a total order)" 70)

definition Well_ord :: "Class \<Rightarrow> bool" ("WOR")
where "WOR(X) \<longleftrightarrow> Rel(X) \<and> (X We (Fld(X)))"
notation Well_ord ("(_ is a well-ordering relation)" 70)
notation Well_ord ("(_ is a wellorder)" 70)

lemma Ex4_28_a: "(Sim W1 W2) \<longrightarrow> (Sim W2 W1)"
oops

lemma Ex4_28_b: "(Sim W1 W2) \<and> (Sim W2 W3) \<longrightarrow> (Sim W1 W3)"
oops

lemma Ex4_28_c: "(Sim \<langle>X,(Abs_Set (Fld(X)))\<rangle> \<langle>Y,(Abs_Set (Fld(Y)))\<rangle>) \<longrightarrow>
                 (TOR(X) \<longleftrightarrow> TOR(Y) \<and> WOR(X) \<longleftrightarrow> TOR(Y))"
oops

(* Ioanna: here goes the definition of order type. *) 

lemma mem_rel_definable: "definable(\<lambda>x::Set.(\<exists>y z::Set. (x = \<langle>y,z\<rangle> \<and> y \<in> z)))"
by(rule belongs_definable) 

definition mem_rel :: Class ("\<E>") 
where "\<E> = {x::Set \<bar> (\<exists>y z::Set. (x = \<langle>y,z\<rangle> \<and> y \<in> z))}"
notation mem_rel ("(the membership relation)" 70)
notation mem_rel ("(the \<in>-relation)" 70)

lemma mem_rel_lemma: "\<forall>x::Set. x \<in> \<E> \<longleftrightarrow> (\<exists>y z::Set. (x = \<langle>y,z\<rangle> \<and> y \<in> z))"
sorry

(* Ioanna: The next two lemmata seems to be necessary for many proofs in this theory, so it doesn't
           get moved to auxiliary03.thy. *)

lemma mem_rel_is_rel: "Rel(\<E>)"
proof-
  {fix x
    assume "x \<in> \<E>"
    from this mem_rel_lemma have "\<exists>y z. x = \<langle>y,z\<rangle>" 
      by (metis Abs_Set_inverse CollectI Ex4_5 universe) 
    from this have "x \<in> \<V> \<times> \<V>" by (simp add: Ex4_9_b cartesian_product_lemma)}
  from this show "Rel \<E>" by (simp add: relation_predicate_def subsetI square)
qed

lemma mem_rel_lemma2: "\<forall>x y::Set. \<langle>x,y\<rangle> \<in> \<E> \<longleftrightarrow> x \<in> y" by (metis B1 mem_rel_lemma)

definition Transitive :: "Class \<Rightarrow> bool" ("Trans")
where "Trans(X) \<longleftrightarrow> (\<forall>u. u \<in> X \<longrightarrow> u \<subseteq> X)"
notation Transitive ("(_ is transitive)" 70)

definition Section :: "Class \<Rightarrow> Class \<Rightarrow> Class \<Rightarrow> bool" ("Sect")
where "Sect Y X Z \<longleftrightarrow> (Z \<subseteq> X \<and> (\<forall>u v::Set.(u \<in> X \<and> v \<in> Z \<and> \<langle>u,v\<rangle> \<in> Y) \<longrightarrow> u \<in> Z))"
(*notation Section ("((3_) is a (1_)-section of (2_))" [71,71,71] 70)*) 


(* Ioanna: page 243 *)

(* Ioanna: Somewhere here also define Y-precedes *)

lemma segment_definable[defining]: "definable(\<lambda>x::Set.(x \<in> X \<and> \<langle>x , Abs_Set W\<rangle> \<in> Y))"
sorry 

definition segment :: "Class \<Rightarrow> Class \<Rightarrow> Class \<Rightarrow> Class" ("Seg")
where "Seg Y X W = {x::Set \<bar> (x \<in> X \<and> \<langle>x , Abs_Set W\<rangle> \<in> Y)}"
notation segment ("(the _-segment of _ determined by _)" 70)

lemma segment_lemma: "\<forall>x. x \<in> (Seg Y X W) \<longleftrightarrow> (x \<in> X \<and> \<langle>x,W\<rangle> \<in> Y)"
sorry 

lemma Ex4_29_a: "Trans(X) \<longleftrightarrow> (\<forall>u v.(v \<in> u \<and> u \<in> X \<longrightarrow> v \<in> X))" 
  using Transitive_def subclass'_def by blast

lemma Ex4_29_b: "Trans(X) \<longleftrightarrow> (\<Union>X \<subseteq> X)" 
proof   
  assume "X is transitive" show "\<Union>X \<subseteq> X"
  proof (rule subsetI)
    fix x::Set
    assume \<Rrightarrow>: "x\<in>\<Union>X"
    obtain y where y: "y\<in>X \<and> x\<in>y" using sum_class_lemma using "\<Rrightarrow>" by auto
    hence "y \<subseteq> X" using Transitive_def \<open>X is transitive\<close> by blast
    moreover thus "x\<in>X" using subclass'_def y by blast
  qed
next  
  assume "\<Union>X\<subseteq>X" thus "X is transitive" unfolding Transitive_def
  by (metis Ex4_1 Ex4_12_g Rep_Set_cases mem_Collect_eq power_class_lemma subclass'_def universe) 
qed


(* Ioanna: the following proof doesn't terminate in my Isabelle2016 *)
(* by blast *)

lemma Ex4_29_c: "Trans(\<emptyset>)" by (simp add: Ex4_29_a empty_set)

lemma Ex4_29_d: "Trans({\<emptyset>})" by (simp add: Ex4_12_b Ex4_29_b empty_set subclass'_def) 

lemma Ex4_29_e: "Trans(X) \<and> Trans(Y) \<longrightarrow> Trans(X \<union> Y) \<and> Trans(X \<inter> Y)"
proof(auto)
  assume 1: "Trans(X)" and 2: "Trans(Y)"
  from this show "Trans(X \<union> Y)" by (metis Ex4_29_a union_iff_or)
  from 1 2 show "Trans(X \<inter> Y)"
    proof -
      {fix x
        assume "x \<in> X \<inter> Y"
        from this have "x \<in> X \<and> x \<in> Y" using Ex4_10_a notin_inter_mono by fastforce
        from this 1 2 Transitive_def have "x \<subseteq> X \<and> x \<subseteq> Y" by (simp add: Transitive_def)
        from this have "x \<subseteq> X \<inter> Y" by (metis Ex4_10_c Ex4_10_e)}
      from this Transitive_def show "Trans(X \<inter> Y)" by simp
    qed
qed

lemma Ex4_29_f: "Trans(X) \<longrightarrow> Trans(\<Union>X)" by (simp add: Ex4_12_e Ex4_29_b)

lemma Ex4_29_g: "(\<forall>u. u \<in> X \<longrightarrow> Trans(u)) \<longrightarrow> Trans(\<Union>X)"
proof -
  {assume 1: "\<forall>u. u \<in> X \<longrightarrow> Trans(u)"
    {fix x
      assume "x \<in> \<Union>X"
      from this have "\<exists>v. x \<in> v \<and> v \<in> X" sorry
      from this obtain v where 2: "x \<in> v \<and> v \<in> X" by blast
      from this 1 have "x \<subseteq> v" by (simp add: Transitive_def)
      from this 2 sum_class_lemma have "x \<subseteq> \<Union>X" using subclass'_def sorry}
    from this have "Trans(\<Union>X)" by (simp add: Transitive_def)}
  from this show ?thesis ..
qed

lemma Ex4_30_a: "\<forall>u::Set.((Seg \<E> X u = X \<inter> u)) \<and> (set(Seg \<E> X u))" 
sorry

lemma Ex4_30_b: "Trans(X) \<longleftrightarrow> (\<forall>u::Set.(u \<in> X \<longrightarrow> Seg \<E> X u = u))" 
sorry

lemma Ex4_30_c: "(\<E> We X) \<and> (Sect \<E> X Z) \<and> Z \<noteq> X \<Longrightarrow> (\<exists>u::Set. u \<in> X \<and> Z = (Seg \<E> X u))"
sorry

definition ordinal :: "Class \<Rightarrow> bool" ("Ord")
where "Ord(X) \<longleftrightarrow> (\<E> We X) \<and> Trans(X)"
notation ordinal ("(_ is an ordinal class)" 70)

lemma ordinals_definable[defining]: "definable(\<lambda>x::Set. Ord(x))"
sorry

definition ordinals :: Class 
where "ordinals = {x::Set \<bar> Ord(x)}"
notation ordinals ("(the class of ordinal numbers)")
notation ordinals ("(the class of all ordinals)")
notation ordinals ("On")

lemma ordinals_lemma: "\<forall>x::Set. x \<in> On \<longleftrightarrow> Ord(x)"
by (simp add: class_comprehension_property ordinals_def ordinals_definable) 

definition ordinal_number :: "Set \<Rightarrow> bool" ("(_ is an ordinal)" 70)
  where "\<alpha> is an ordinal \<longleftrightarrow> Ord(Rep_Set \<alpha>) \<and> (\<alpha> is a set)"

(* Ioanna: The remarks under the definition of On belong to the proof of ordinals_definable. *)

(* page 244 *)

lemma Ex4_31_a: "\<emptyset> \<in> On"
proof -
  have "\<E> We \<emptyset>" using Irrefl_rel_on_def empty_set Well_ord_of_def mem_rel_is_rel
    by (metis Ex4_10_d Ex4_10_j)
  have "Trans(\<emptyset>)" by (simp add: Ex4_29_c)
  from this \<open>\<E> We \<emptyset>\<close> show ?thesis 
    by (simp add: ordinals_lemma ordinal_def)
qed

lemma Ex4_31_b: "{\<emptyset>} \<in> On"
proof -
  have "\<E> We {\<emptyset>}"
  proof(unfold Well_ord_of_def, auto)
    show "\<E> Irr {\<emptyset>}"
      by (metis Irrefl_rel_on_def empty_set singletonE 
                mem_rel_lemma2 mem_rel_is_rel)
    next show "\<And>Z. Z \<subseteq> Rep_Set {\<emptyset>} \<Longrightarrow> Z \<noteq> Rep_Set \<emptyset> \<Longrightarrow>
      \<exists>y. Rep_Set y \<in> Z \<and> (\<forall>v. Rep_Set v \<in> Z \<and> v \<noteq> y \<longrightarrow> Rep_Set \<langle>y, v\<rangle> \<in> \<E> \<and>
      Rep_Set \<langle>v, y\<rangle> \<notin> \<E>)"
      by (metis Ex4_10_a Ex4_10_c Rep_Set_inverse empty_is_unique notin_inter_mono pairing)
  qed
  have "Trans({\<emptyset>})" by (simp add: Ex4_29_d)
  from this \<open>\<E> We {\<emptyset>}\<close> show ?thesis by (simp add: ordinals_lemma ordinal_def)
qed

text{* \begin{quote}
       We shall use lower-case Greek letters $\alpha$, $\beta$, $\gamma$, $\delta$,
       $\tau$, $\dots$ as restricted variables for ordinal numbers. Thus, 
       $(\forall\alpha)\mathcal{B}(\alpha)$ stands for 
       $(\forall x)(x \in On \Rightarrow \mathcal{B}(x))$, and 
       $(\exists\alpha)\mathcal{B}(\alpha)$ stands for 
       $(\exists x)(x \in On \land \mathcal{B}(x))$.
       \end{quote} 

We shall use the bounded quantifiers we defined between sets and classes, in NBG_Set.thy.
We could consider dealing with the ordinals as a subtype of set, if it were easier to deal
with subtypes. 
*} 


lemma Prop4_8_a: "\<forall>X. Ord(X) \<longrightarrow> (X \<notin> X \<and> (\<forall>u::Set. (u \<in> X \<longrightarrow> u \<notin> u)))"
--"Hence, X\<notin>X."
proof (rule allI, rule impI)
  fix X
  assume 1: "Ord(X)" --"If Ord(X),"
  from this have "\<E> Irr X" by (simp add: ordinal_def Well_ord_of_def)
    --"then \<E> is irreflexive on X;"
  hence *: "\<forall>u::Set. (u \<in> X \<longrightarrow> u\<notin>u)" by (simp add: Irrefl_rel_on_def mem_rel_lemma2) 
     --"so, (\<forall>u)(u \<in> X \<longrightarrow> u\<notin>u);" 
  have "X \<notin> X" 
  proof (rule ccontr)
    assume "\<not>(X\<notin>X)" hence "X\<in>X" by simp --"and, if X\<in>X,"
    hence "X\<notin>X" --"X\<notin>X."
      proof -
        from \<open>X \<in> X\<close> have "set X" using Ex4_5 by blast 
        from this  have "\<exists>x::Set. Rep_Set x = X" by (metis CollectI Rep_Set_cases universe)
        from this obtain x where "Rep_Set x = X" by blast
        from this \<open>X \<in> X\<close> * show ?thesis using Irrefl_rel_on_def mem_rel_lemma2 by blast
      qed
    thus False by (simp add: \<open>X \<in> X\<close>) 
  qed --"Hence, X\<notin>X."
  thus "(X \<notin> X \<and> (\<forall>u::Set. (u \<in> X \<longrightarrow> u \<notin> u)))" using * by simp
qed

lemma Prop4_8_b: "(Ord(X) \<and> Y \<subset> X \<and> Trans(Y)) \<longrightarrow> Y \<in> X"
 proof auto
  assume 1: "Ord(X)" and 2: "Y \<subset> X" and "Trans(Y)" --"Assume Ord(X) \<and> Y \<subset> X \<and> Trans(Y)."
  hence "Sect \<E> X Y" 
     by (metis Ex4_30_b Section_def segment_lemma mem_rel_lemma2 strict_subclass_def)
    --"It is easy to see that Y is a proper \<E>-section of X."
  thus "Y \<in> X" using Ex4_30_c Ex4_30_b 1 2 ordinal_def strict_subclass_def by force
    --"Hence, by Exercise 4.30(b,c), Y\<in>X."
 qed

lemma Prop4_8_c: "Ord(X) \<and> Ord(Y) \<Longrightarrow> (Y \<subset> X \<longleftrightarrow> Y \<in> X)"
proof (cases "X = On")
  assume 1: "Ord X \<and> Ord Y" and 2: "X = On"
  from this show "Y \<subset> X \<longleftrightarrow> Y \<in> X"
  proof auto
    assume "Y \<subset> On"
    from this 1 2 show "Y \<in> On" using ordinal_def Prop4_8_b by auto
    next assume "Y \<in> On"
    from this 2 1 have 3: "Y \<subseteq> On" using Ex4_29_a ordinal_def subset by blast
    from 1 have 4: "\<E> Irr X" by (simp add: ordinal_def Well_ord_of_def)
    {assume "Y = On"
      from this \<open>Y \<in> On\<close> have "Y \<in> Y" by simp
      from this 4 have False
      proof -
        from \<open>Y \<in> Y\<close> have "set Y" using Ex4_5 Ex4_1 by blast 
        from this have "\<exists>y::Set. Rep_Set y = Y" by (metis CollectI Rep_Set_cases universe)
        from this obtain y where "Rep_Set y = Y" by blast
        from this \<open>Y \<in> Y\<close> 1 show False using Prop4_8_a by blast
      qed}
    from this have "Y \<noteq> On" by blast
    from this 3 strict_subclass_def show "Y \<subset> On" by simp
  qed
  next assume "Ord X \<and> Ord Y" and "X \<noteq> On"
  from this show "Y \<subset> X \<longleftrightarrow> Y \<in> X"
    by (metis ordinal_def Prop4_8_a Prop4_8_b Transitive_def strict_subclass_def)
qed

lemma Prop4_8_d: "(Ord(X) \<and> Ord(Y)) \<Longrightarrow> ((X \<in> Y \<or> X = Y \<or> Y \<in> X) \<and> \<not>(X \<in> Y \<and> Y \<in> X) 
                                                               \<and> \<not>(X \<in> Y \<and> X = Y))"
proof
  assume 1: "Ord X \<and> Ord Y"
  {assume "X \<noteq> Y"
    have "X \<inter> Y \<subseteq> X" and "X \<inter> Y \<subseteq> Y" by (metis Ex4_10_a Ex4_10_c Ex4_10_e Ex4_10_g)+
    from 1 have "Trans(X \<inter> Y)" by (simp add: Ex4_29_e ordinal_def)
    {assume "X \<inter> Y \<subset> X" and "X \<inter> Y \<subset> Y"
      from this 1 \<open>Trans (X \<inter> Y)\<close> have "X \<inter> Y \<in> X" and "X \<inter> Y \<in> Y" by (simp add: Prop4_8_b)+
      from this have "X \<inter> Y \<in> X \<inter> Y" 
        by (metis Abs_Set_inverse B2 Ex4_10_o Quotient_Set V_Co_Empty eq_onp_to_Domainp
          mem_Collect_eq union_iff_or)
      from this 1 Prop4_8_a \<open>X \<inter> Y \<in> X\<close> \<open>X \<inter> Y \<in> Y\<close> \<open>X \<noteq> Y\<close> have "False" sorry}
    from this \<open>X \<inter> Y \<subseteq> X\<close> \<open>X \<inter> Y \<subseteq> Y\<close> strict_subclass_def have "X \<inter> Y = X \<or> X \<inter> Y = Y" by blast
    from this \<open>X \<noteq> Y\<close> \<open>X \<inter> Y \<subseteq> X\<close> \<open>X \<inter> Y \<subseteq> Y\<close> strict_subclass_def have "X \<subset> Y \<or> Y \<subset> X" by auto
    from 1 this have "X \<in> Y \<or> Y \<in> X" using ordinal_def Prop4_8_b by blast}
  from this show "X \<in> Y \<or> X = Y \<or> Y \<in> X" by blast
  from 1 show "\<not> (X \<in> Y \<and> Y \<in> X) \<and> \<not> (X \<in> Y \<and> X = Y)" 
    using Prop4_1_a Prop4_8_c strict_subclass_def by auto
qed

lemma Prop4_8_e: "(Ord(X) \<and> Rep_Set Y \<in> X) \<longrightarrow> Y \<in> On"
proof(simp add: ordinals_lemma ordinal_def, auto)
  assume 1: "\<E> We X" and 2: "Trans X" and 3: "Y \<in> X"
  from this show "\<E> We Y" using Ex4_25 Transitive_def by blast
  {fix u v::Set
    assume "u \<in> Y" and "v \<in> u"
    from this 2 3 have "v \<in> X" and "u \<in> X" using Ex4_29_a by blast+
    from 1 have "\<E> Con X" using Ex4_24 Tot_ord_on_def by blast
    from this 3 \<open>v \<in> X\<close> have "v \<in> Y \<or> v = Y \<or> Y \<in> v" 
      using Conn_rel_on_def mem_rel_lemma2 by blast
    from this have "v \<in> Y"
    proof(rule, clarify, auto)
      from 1 have "\<E> Tr X" using Ex4_24 Tot_ord_on_def by auto
      {assume "v = Y"
        from this \<open>u \<in> Y\<close> \<open>v \<in> u\<close> \<open>u \<in> X\<close> \<open>\<E> Tr X\<close> 3 show "Y \<in> Y"
          using Trans_rel_on_def mem_rel_lemma2 by blast}
      {assume "Y \<in> v"
        from this \<open>u \<in> Y\<close> \<open>v \<in> u\<close> \<open>u \<in> X\<close> \<open>\<E> Tr X\<close> \<open>v \<in> X\<close> 3 have "u \<in> u"
          using Ex4_5 Ex4_23 by (meson Trans_rel_on_def mem_rel_lemma2) 
        from this 1 2 3 \<open>u \<in> X\<close> \<open>u \<in> Y\<close> \<open>v \<in> X\<close> show "v \<in> Y"
          by (metis ordinal_def Prop4_8_a)}
    qed}
  from this show "Trans(Y)" 
    by (metis Ex4_10_p Ex4_10_s Ex4_29_a Rep_Set_cases mem_Collect_eq notin_inter_mono)
qed

lemma Prop4_8_f: "\<E> We On"
proof(unfold Well_ord_of_def, auto)
  show "\<E> Irr On"
    by (meson Irrefl_rel_on_def ordinals_lemma ordinal_def Well_ord_of_def
              mem_rel_lemma2 mem_rel_is_rel)
  next {fix Z
    assume "Z \<subseteq> On" and "Z \<noteq> \<emptyset>"
    fix \<alpha>::Set
    assume "\<alpha> \<in> Z"
    have "(\<forall>v. v \<in> Z \<and> v \<noteq> \<alpha> \<longrightarrow> \<langle>\<alpha>, v\<rangle> \<in> \<E> \<and> \<langle>v, \<alpha>\<rangle> \<notin> \<E>) \<or>
      \<not>(\<forall>v. v \<in> Z \<and> v \<noteq> \<alpha> \<longrightarrow> \<langle>\<alpha>, v\<rangle> \<in> \<E> \<and> \<langle>v, \<alpha>\<rangle> \<notin> \<E>)" by blast
    from this have "\<exists>y. Rep_Set y \<in> Z \<and> (\<forall>v. Rep_Set v \<in> Z \<and> v \<noteq> y 
                                         \<longrightarrow> Rep_Set \<langle>y, v\<rangle> \<in> \<E> \<and> Rep_Set \<langle>v, y\<rangle> \<notin> \<E>)"
    proof
      assume "\<forall>v. v \<in> Z \<and> v \<noteq> \<alpha> \<longrightarrow> \<langle>\<alpha>, v\<rangle> \<in> \<E> \<and> \<langle>v, \<alpha>\<rangle> \<notin> \<E>"
      from this \<open>\<alpha> \<in> Z\<close> show ?thesis by blast
      next assume 1: "\<not> (\<forall>v. Rep_Set v \<in> Z \<and> v \<noteq> \<alpha> \<longrightarrow> Rep_Set \<langle>\<alpha>, v\<rangle> \<in> \<E> \<and> Rep_Set \<langle>v, \<alpha>\<rangle> \<notin> \<E>)"
      from this \<open>\<alpha> \<in> Z\<close> \<open>Z \<subseteq> On\<close> have "\<E> We \<alpha>" 
        by (metis Ex4_10_d ordinals_lemma ordinal_def union_iff_or)
      from 1 \<open>\<alpha> \<in> Z\<close> \<open>Z \<subseteq> On\<close> have "Z \<inter> \<alpha> \<noteq> \<emptyset>" 
          by (metis B2 Ex4_10_d empty_set ordinals_lemma
                    Prop4_8_d Rep_Set_inject mem_rel_lemma2 union_iff_or)
      have "Z \<inter> \<alpha> \<subseteq> \<alpha>" using B2 subsetI by blast
      from this \<open>Z \<inter> \<alpha> \<noteq> \<emptyset>\<close> \<open>\<E> We \<alpha>\<close> have "\<exists>\<beta>. \<beta> \<in> (Z \<inter> \<alpha>) \<and>
        (\<forall>v. (v \<in> (Z \<inter> \<alpha>) \<and> v \<noteq> \<beta>) \<longrightarrow> \<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>)" using Well_ord_of_def by blast
      from this obtain \<beta> where b1: "\<beta> \<in> (Z \<inter> \<alpha>)" 
                           and b2: "\<forall>v. (v \<in> (Z \<inter> \<alpha>) \<and> v \<noteq> \<beta>) \<longrightarrow> \<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>"
        by blast
      from this have "\<forall>v. (v \<in> Z \<and> v \<noteq> \<beta>) \<longrightarrow> \<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>"
      proof -
        {fix v::Set
          assume "v \<in> Z" and "v \<noteq> \<beta>"
          from this \<open>\<alpha> \<in> Z\<close> \<open>Z \<subseteq> On\<close> have v: "v \<in> \<alpha> \<or> v = \<alpha> \<or> \<alpha> \<in> v"
            by (metis B2 Ex4_10_c ordinals_lemma Prop4_8_d Rep_Set_inject)
          {assume "v \<in> \<alpha>"
            from this b2 \<open>v \<in> Z\<close> \<open>v \<noteq> \<beta>\<close> have "\<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>" using B2 by blast}
          from this have v1: "v \<in> \<alpha> \<Longrightarrow> \<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>" by simp
          {assume "v = \<alpha>"
            from this \<open>v \<in> Z\<close> \<open>Z \<subseteq> On\<close> b1 have "\<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>"
              by (metis B2 Ex4_30_a ordinals_lemma Prop4_8_d segment_lemma subset)}
          from this have v2: "v = \<alpha> \<Longrightarrow> \<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>" by simp
          {assume "\<alpha> \<in> v"
            from this \<open>v \<in> Z\<close> \<open>\<alpha> \<in> Z\<close> \<open>Z \<subseteq> On\<close> b1 have "\<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>"
              by (metis Ex4_10_a Ex4_10_c Ex4_30_a ordinals_lemma ordinal_def segment_lemma 
                        Transitive_def notin_inter_mono v1)}
          from this have v3: "\<alpha> \<in> v \<Longrightarrow> \<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>" by simp
          from v v1 v2 v3 have "\<langle>\<beta>,v\<rangle> \<in> \<E> \<and> \<langle>v,\<beta>\<rangle> \<notin> \<E>" by blast}
        from this show ?thesis by blast
      qed
      from this show ?thesis using b1 notin_inter_mono by blast
    qed}
  from this show "\<And>Z. Z \<subseteq> On \<Longrightarrow> Z \<noteq> Rep_Set \<emptyset>
    \<Longrightarrow> \<exists>y. Rep_Set y \<in> Z \<and> (\<forall>v. Rep_Set v \<in> Z \<and> v \<noteq> y 
                              \<longrightarrow> Rep_Set \<langle>y, v\<rangle> \<in> \<E> \<and> Rep_Set \<langle>v, y\<rangle> \<notin> \<E>)"
    by (metis empty_set Prop4_1_a subsetI)
qed

lemma Prop4_8_g: "Ord(On)"
by (metis Ex4_12_f Ex4_29_b Ex4_29_f ordinals_lemma ordinal_def Prop4_8_e 
          Prop4_8_f power_class_lemma subset)

lemma Prop4_8_h: "\<not>set(On)"
by (metis Abs_Set_inverse ordinals_lemma Prop4_8_a Prop4_8_g mem_Collect_eq 
          universe)



lemma "(\<forall>x::Set. \<exists>y::Set. P x y) \<Longrightarrow> (\<exists>f::Set\<Rightarrow>Set. \<forall>z::Set. P z (f(z)))"
using Hilbert_Choice.choice .  


lemma Prop4_8_i: "Ord(X) \<Longrightarrow> X = On \<or> X \<in> On"
using Prop4_8_d Prop4_8_g Prop4_8_h proper_class_predicate_def set_predicate_def by auto

lemma Prop4_8_j: "y \<subset> On \<and> Trans(y) \<Longrightarrow> y \<in> On" (* Fehler bei Mendelson: \<subseteq> *)
by (metis Prop4_8_b Prop4_8_g)

lemma Prop4_8_k: "x \<in> On \<and> y \<in> On \<Longrightarrow> (x \<subseteq> y \<or> y \<subseteq> x)"
by (metis Abs_Set_inverse CollectI ordinals_lemma ordinal_def Prop4_8_d Transitive_def 
          set_predicate_def subclass'_def universe)

(* Ioanna: page 245 *)

definition less_on_ordinals :: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "<\<^sub>o" 70)
where "x <\<^sub>o y \<longleftrightarrow> (x \<in> On \<and> y \<in> On \<and> x \<in> y)"

definition leq_on_ordinals :: "Class \<Rightarrow> Class \<Rightarrow> bool" (infixl "\<le>\<^sub>o" 70)
where "x \<le>\<^sub>o y \<longleftrightarrow> y \<in> On \<and> (x = y \<or> x <\<^sub>o y)"


lemma less_on_ordinals_remark1: 
"\<forall>x y::Set. ((x is an ordinal) \<and> (y is an ordinal))\<longrightarrow> ((x <\<^sub>o y) \<longleftrightarrow> (x \<in> y))"
unfolding less_on_ordinals_def using ordinal_number_def ordinals_lemma by simp

(* Ioanna: Also add second remark: 
           lemma less_on_ordinals_remark2: "<\<^sub>o well orders On" *) 

lemma Transfinite_Induction: "(\<forall>\<beta>\<in>On. (\<forall>\<alpha>\<in>On. (\<alpha> \<in> \<beta> \<longrightarrow> \<alpha> \<in> X) \<longrightarrow> \<beta> \<in> X)) \<longrightarrow> On \<subseteq> X"
text{* \begin{quote}
       If, for every $\beta$, whenever all ordinals less than $\beta$ are in $X$, $\beta$ must
       also be in $X$, then all ordinals are in $X$.\\
       Proof. \\
       Assume "$(\forall \beta)[(\forall\alpha)(\alpha\in\beta\Rightarrow\alpha\in X)
       \Rightarrow \beta\in X]$. Assume there is an ordinal in $On-X$. Then, 
       since $On$ is well-ordered by $E$, there is a least ordinal $\beta$ in
       $On-X$. Hence, all ordinals less than $\beta$ are in $X$. So, by hypothesis, 
       $\beta$ is in X, which is a contradiction.
       \end{quote} *}     
proof (rule impI, rule ccontr)
  assume premise: "\<forall>\<beta> \<in>On. (\<forall>\<alpha>\<in>On. (\<alpha> \<in> \<beta> \<longrightarrow> \<alpha> \<in> X) \<longrightarrow> \<beta> \<in> X)"
  --"Assume \<forall>\<beta> \<in>On. (\<forall>\<alpha>\<in>On. (\<alpha> \<in> \<beta> \<longrightarrow> \<alpha> \<in> X) \<longrightarrow> \<beta> \<in> X)"
  assume contra:  "\<not>(On\<subseteq>X)" --"Mendelson doesn't see a difference between this and the next."
  hence *: "\<exists>\<gamma>\<in>On. \<gamma>\<in>(On\<setminus>X)" using Ex4_9_c exists_in_def subsetI by metis
  --"Assume there is an ordinal in On-X."
  hence "(On\<setminus>X) has a least element with respect to \<E>" using Prop4_8_f 
  --"Then, since On is well-ordered by E,"
  proof -  --"This is considered an obvious step in Mendelson."
    have "(On\<setminus>X)\<noteq>\<emptyset>" using * empty_set exists_in_def by auto 
    moreover have "(On\<setminus>X)\<subseteq>On" using B2 subsetI by blast 
    thus ?thesis using Prop4_8_f unfolding Well_ord_of_def using calculation by blast 
  qed
  then obtain \<beta> where **: "\<beta> is the least in (On\<setminus>X) with respect to \<E>" by auto
  --"there is a least ordinal \<beta> in On-X."
  hence "\<forall>\<gamma>\<in>On. (\<gamma> <\<^sub>o \<beta> \<longrightarrow> \<gamma>\<in>X)" using premise Ex4_31_a empty_set forall_in_def
    by auto
  --"Hence, all ordinals less than \<beta> are in X."
  thus False using premise unfolding less_on_ordinals_def 
    using Ex4_31_a Ex4_9_c empty_set Rep_Set_inverse ** forall_in_def notin_inter_mono 
    by auto 
  --"So, by hypothesis, \<beta> is in X, which is a contradiction."
qed  

lemma Transfinite_Induction1_remark: 
  fixes X:: Class
  fixes \<B>:: "Set \<Rightarrow> bool"
  assumes 0: "definable(\<B>)"
  assumes 1: "X = {x \<bar> (\<B>(x) \<and> x\<in>On)}"
  assumes 2: "\<forall>\<beta>\<in>On. (\<forall>\<alpha>\<in>On. (\<alpha>\<in>\<beta> \<longrightarrow> \<B>(\<alpha>)) \<longrightarrow> \<B>(\<beta>))"
  shows "On\<subseteq>X"
proof - --"This in Mendelson does not require a proof, it is considered obvious."
  have *: "definable(\<lambda>x. \<B>(x) \<and> x\<in>On)" by (simp add: "0" and_definable belongs_definable_lemma) 
  have "\<forall>\<beta>\<in>On. (\<forall>\<alpha>\<in>On. (\<alpha> \<in> \<beta> \<longrightarrow> \<alpha> \<in> X) \<longrightarrow> \<beta> \<in> X)" unfolding forall_in_def
  proof (rule allI, rule impI, rule allI, rule impI, rule impI)
    fix \<alpha> \<beta>::Set assume "\<beta>\<in>On" and "\<alpha>\<in>On" and "\<alpha> \<in> \<beta> \<longrightarrow> \<alpha> \<in> X"
    hence "\<B>(\<beta>)" using 0 1 2 Ex4_31_a empty_set forall_in_def by auto  
    thus "\<beta>\<in>X" using 0 1 * \<open>\<beta> \<in> On\<close> comprehensionI by blast 
  qed
  thus ?thesis using Transfinite_Induction by simp
qed
  
(* Ioanna: page 246 *)

definition successor :: "Set \<Rightarrow> Set" ("succ")
where "succ(X) \<equiv> Abs_Set(X \<union> {X})"


(* Ioanna: The following lemma justifies defining successor to have range Set *)
lemma "\<forall>x::Set. set(X\<union>{X})" by (simp add: Ex4_13_b)

lemma Prop4_10_a: "\<forall>x::Set. x \<in> On \<longleftrightarrow> succ x \<in> On"
proof (rule allI)
  fix x::Set
  have "x\<in> succ(x)" unfolding successor_def 
    by (simp add: Abs_Set_inverse Ex4_13_b Ex4_9_a singletonE2 universe) 
    --"x\<in>x'."
  hence *: "succ(x) \<in> On \<longrightarrow> x \<in> On" using Prop4_8_e using ordinals_lemma by blast
    --"Hence, if x'\<in>On, then x\<in>On by Proposition 4.8(e)."
  have "x\<in>On \<longrightarrow> succ(x)\<in>On" --"Conversely,"
  proof 
    assume "x\<in>On" --"assume x\<in>On."
    show "succ(x)\<in>On" 
    proof -
      have "\<E> We (x\<union>{x})" and "Trans(x\<union>{x})" --"We must prove E We (x\<union>{x}) and Trans(x\<union>{x})."
      proof -
        show "\<E> We (x\<union>{x})" unfolding Well_ord_of_def
        proof 
          have "\<E> We x" using \<open>x \<in> On\<close> ordinal_def ordinals_lemma by blast 
            --"Since E We x"
          moreover have "x\<notin>x" using Prop4_8_d \<open>x \<in> On\<close> ordinals_lemma by blast
            --"and x\<notin>x,"
          thus "\<E> Irr (x\<union>{x})" 
            using Ex4_9_a Irrefl_rel_on_def Prop4_8_a \<open>x \<in> On\<close> mem_rel_is_rel mem_rel_lemma2 
                  ordinals_lemma pairing by auto 
            --"E Irr (x\<union>{x})." 
          show " \<forall>y. (y \<subseteq> (x \<union>{x}) \<and> (y \<noteq> \<emptyset>)) \<longrightarrow> 
                  (y has a least element with respect to the \<in>-relation)"
          proof (rule allI, rule impI)
            fix y
            assume *: "(y \<subseteq> (x \<union>{x}) \<and> (y \<noteq> \<emptyset>))" --"Also, if y\<noteq>\<emptyset> \<and> y\<subseteq>x\<union>{x},"
            show "(y has a least element with respect to the \<in>-relation)"
            proof (cases "y={x}")
              assume "y={x}" --"then either y={x},"
              hence "x is the least in y with respect to \<E>" by (simp add: Rep_Set_inject pairing) 
                --"in which case the least element of y is x,"
              thus ?thesis by blast 
              next 
              assume **: "y\<noteq>{x}" 
              have ***: "y\<inter>x \<noteq> \<emptyset>" --"or y\<inter>x\<noteq>\<emptyset>"
              (* Sledgehammer could not bridge this, not even with "help". *)
              proof (rule ccontr)
                assume "\<not>(y\<inter>x \<noteq> \<emptyset>)" hence "y\<inter>x = \<emptyset>" by simp
                hence "y\<subseteq>{x}" using * by (metis Ex4_10_b Ex4_10_c Ex4_10_j Ex4_10_u) 
                hence "y={x}" using * subset_of_singleton[where b="y" and c="x"] by simp
                thus False using ** by simp
              qed
              have "y\<inter>x \<subseteq> x" using  Ex4_10_c Ex4_10_e Ex4_10_g by simp
              hence "(y\<inter>x) has a least element with respect to \<E>" 
                using \<open>\<E> We x\<close> *** Well_ord_of_def by blast
              then obtain u::Set where u: "u is the min(y\<inter>x) wrt. \<E> " by blast
                --"and the least element of y\<inter>x"
              have "u is the least in y with respect to \<E>" --"is then the least element of y."
              (* Again, Sledgehammer could not bridge this, not even with "help". *)
              proof 
                show "u\<in>y" using u B2 by blast 
                show "\<forall>v::Set. (v \<in> y \<and> v \<noteq> u \<longrightarrow> (\<langle>u, v\<rangle> \<in> \<E> \<and> \<langle>v, u\<rangle> \<notin> \<E>)) "
                proof (rule allI, rule impI, rule conjI)
                  fix v::Set
                  assume "v\<in>y \<and> v\<noteq>u"
                  show "\<langle>u,v\<rangle> \<in> \<E>" sorry
                  show "\<langle>v,u\<rangle> \<notin> \<E>" by (metis B2 Prop4_8_d Prop4_8_e \<open>\<langle>u, v\<rangle> \<in> \<E>\<close> \<open>x \<in> On\<close> 
                                             mem_rel_lemma2 ordinals_lemma u) 
                qed
              qed
              thus ?thesis by blast 
            qed 
          qed  
        qed --"Hence, E We (x\<union>{x})."
        show "Trans(x\<union>{x})" unfolding Transitive_def
        proof (rule allI, rule impI, rule subclassI)
          fix y u
          assume "y\<in>x\<union>{x}" and "u\<in>y" --"In addition, if y\<in>x\<union>{x} and u\<in>y,"
          hence "u\<in>x" using Ex4_29_a \<open>x \<in> On\<close> singletonE ordinal_def ordinals_lemma 
            union_iff_or by blast 
             --"then u\<in>x."
          thus "u\<in>(x\<union>{x})" using unionI1 by blast 
        qed --"Thus Trans(x\<union>{x})."
      qed
      thus ?thesis unfolding successor_def ordinals_def ordinal_def sorry
    qed
  qed
  thus "x \<in> On \<longleftrightarrow> succ x \<in> On" using * by auto
qed

lemma Prop4_10_b: "\<forall>\<alpha>\<in>On. \<not>(\<exists>\<beta>\<in>On. \<alpha> <\<^sub>o \<beta> \<and> \<beta> <\<^sub>o succ(\<alpha>))" unfolding forall_in_def
--"Assume \<open>\<alpha> <\<^sub>o \<beta> <\<^sub>o \<alpha>'\<close>. Then, \<alpha>\<in>\<beta> \<and> \<beta> \<in> \<alpha>'. Since \<alpha>\<in>\<beta>, \<beta>\<notin>\<alpha> and \<beta>\<noteq>\<alpha> by Proposition 4.8(d), 
contradicting \<beta>\<in>\<alpha>'"
proof (rule allI, rule impI, rule ccontr, auto) 
  fix \<alpha>::Set
  assume "\<alpha>\<in>On"
  assume "\<exists>\<beta>\<in>On. \<alpha> <\<^sub>o \<beta> \<and> \<beta> <\<^sub>o succ(\<alpha>)"
  then obtain \<beta>::Set where "\<beta>\<in>On \<and> \<alpha> <\<^sub>o \<beta> \<and> \<beta> <\<^sub>o succ(\<alpha>)" using exists_in_def by auto 
  hence *: "\<alpha>\<in>\<beta> \<and> \<beta> \<in> succ(\<alpha>)" using less_on_ordinals_def by blast 
  hence "\<beta>\<notin>\<alpha> \<and> \<beta>\<noteq>\<alpha>" using Prop4_8_d Ex4_29_a \<open>\<alpha> \<in> On\<close> ordinal_def ordinals_lemma by blast
  thus False 
  proof -
    have "\<beta>\<in>succ(\<alpha>)" using * by simp
    hence "\<beta>\<in>(\<alpha>\<union>{\<alpha>})" unfolding successor_def 
      using Abs_Set_inverse Rep_Set_inverse Ex4_13_b mem_Collect_eq universe by simp
    thus False by (simp add: Ex4_9_a Rep_Set_inject \<open>\<beta> \<notin> \<alpha> \<and> \<beta> \<noteq> \<alpha>\<close> pairing) 
  qed 
qed


lemma Prop4_10_c: "\<forall>\<alpha>\<in>On. \<forall>\<beta>\<in>On. (succ \<alpha> = succ \<beta> \<longrightarrow> \<alpha> = \<beta>)"
--"Assume succ(\<alpha>)=succ(\<beta>). Then \<open>\<beta><\<^sub>o succ(\<alpha>)\<close> and, by part (b), \<open>\<beta> \<le>\<^sub>o \<alpha>\<close>.  Similarly, \<open>\<alpha> \<le>\<^sub>o \<beta>\<close>. 
   Hence, \<alpha>=\<beta>."
unfolding forall_in_def 
proof (rule allI, rule impI, rule allI, rule impI, rule impI)
  fix \<alpha> \<beta>::Set assume a: "\<alpha>\<in>On" and b: "\<beta>\<in>On"
  hence a_suc: "succ(\<alpha>)\<in>On" and b_suc: "succ(\<beta>)\<in>On" using Prop4_10_a by (blast, blast)
  assume *: "succ(\<alpha>) = succ(\<beta>)"
  hence "\<beta>\<in>succ(\<alpha>)" unfolding successor_def by (simp add: Abs_Set_inverse Ex4_13_b Ex4_9_a 
    singletonE2 universe) 
  (* the step above wasn't bridged by Sledgehammer. In the similar case below, I put all the
     lemmas that appeared above and below, and then Sledgehammer can find the proof with metis 
     in the proof of "\<alpha> <\<^sub>o succ(\<beta>)". *)
  hence "\<beta> <\<^sub>o succ(\<alpha>)" using less_on_ordinals_def[where x=\<beta> and y="succ(\<alpha>)"] a_suc b 
    unfolding successor_def by simp
  hence **: "\<beta> \<le>\<^sub>o \<alpha>" using a Prop4_10_b Prop4_8_d leq_on_ordinals_def less_on_ordinals_def 
    ordinals_lemma unfolding exists_in_def forall_in_def by metis 
  from * have "\<alpha> <\<^sub>o succ(\<beta>)" unfolding successor_def using Abs_Set_inverse Ex4_13_b Ex4_9_a
    singletonE2 universe b_suc a less_on_ordinals_def[where x=\<alpha> and y="succ(\<beta>)"]
    by (metis mem_Collect_eq successor_def) 
  hence "\<alpha> \<le>\<^sub>o \<beta>" using b Prop4_10_b Prop4_10_b Prop4_8_d  leq_on_ordinals_def less_on_ordinals_def 
    ordinals_lemma unfolding exists_in_def forall_in_def by metis 
  thus "\<alpha> = \<beta>" using ** using Prop4_8_d Rep_Set_inject leq_on_ordinals_def less_on_ordinals_def 
    ordinals_lemma by auto 
qed

lemma Ex4_32: "\<forall>\<alpha>\<in>On. \<alpha> \<subset> succ \<alpha>"
sorry

(* Ioanna: "Suc" is Isabelle's successor function for Isabelle's natural numbers. *) 
definition succ_ord :: "Class \<Rightarrow> bool" ("succ_ord")
where "succ_ord(X) \<longleftrightarrow> X \<in> On \<and> (\<exists>\<alpha>. X = succ \<alpha>)"
notation succ_ord ("_ is a successor ordinal" 70)
notation succ_ord ("_ is a successor" 70)

lemma ord_of_first_kind_definable[defining]: "definable(\<lambda>x::Set. x = \<emptyset> \<or> succ_ord(x))"
sorry

definition ord_of_first_kind :: Class ("K1")
where "K1 \<equiv> {x::Set \<bar> x = \<emptyset> \<or> succ_ord(x)}"
notation ord_of_first_kind ("K\<^sub>1")

lemma ord_of_first_kind_lemma: "\<forall>x::Set. x \<in> K1 \<longleftrightarrow> x = \<emptyset> \<or> succ_ord(x)"
by (metis (mono_tags, lifting) class_comprehensionE(2) comprehensionI 
           ord_of_first_kind_def ord_of_first_kind_definable)

lemma omega_definable[defining]: "definable(\<lambda>x::Set. x \<in> K1 \<and> (\<forall>u::Set. u \<in> x \<longrightarrow> u \<in> K1))"
sorry

definition omega :: Class ("\<omega>")
where "\<omega> \<equiv> {x::Set \<bar> x \<in> K1 \<and> (\<forall>u::Set. u \<in> x \<longrightarrow> u \<in> K1)}"

lemma omega_lemma: "\<forall>x::Set. x \<in> \<omega> \<longleftrightarrow> (x \<in> K1 \<and> (\<forall>u::Set. u \<in> x \<longrightarrow> u \<in> K1))"
sorry


lemma zero_in_omega: "\<emptyset> \<in> \<omega>"
sorry

lemma one_in_omega: "{\<emptyset>} \<in> \<omega>"
sorry


lemma Prop4_11_a: "\<forall>\<alpha>\<in>On. \<alpha> \<in> \<omega> \<longleftrightarrow> succ(\<alpha>) \<in> \<omega>" unfolding forall_in_def

--"Assume \<alpha>\<in>\<omega>. Since Suc(\<alpha>\<acute>), \<alpha>\<acute>\<in>K1. Also, if \<beta>\<in>\<alpha>\<acute>, then \<beta>\<in>\<alpha> or \<beta>=\<alpha>. Hence \<beta>\<in>K1. 
   Thus, \<alpha>\<acute>\<in>\<omega>. Conversely, if \<alpha>\<acute>\<in>\<omega>, then, since \<alpha>\<in>\<alpha>\<acute> and \<forall>\<beta>\<in>On. \<beta>\<in>\<alpha> \<longrightarrow> \<beta>\<in>\<alpha>\<acute>),
   it follows that \<alpha>\<in>\<omega>."

proof (rule allI, rule impI, rule iffI)
  fix \<alpha>::Set  assume "\<alpha>\<in>On" and "\<alpha>\<in>\<omega>"
  have "(succ(\<alpha>)) is a successor ordinal" using Prop4_10_a \<open>\<alpha> \<in> On\<close> succ_ord_def by auto 
  hence *: "(succ(\<alpha>))\<in>K\<^sub>1" by (simp add: ord_of_first_kind_lemma) 
  have "(\<forall>\<beta>::Set. \<beta> \<in> (succ(\<alpha>)) \<longrightarrow> \<beta> \<in> K1)" 
  proof (rule allI, rule impI)
    fix \<beta>::Set assume "\<beta> \<in> succ(\<alpha>)"
    hence "\<beta>\<in>\<alpha> \<or> \<beta>=\<alpha>" unfolding successor_def union_iff_or 
      using Abs_Set_inverse Ex4_13_b Ex4_9_a ex_definable_lemma1 universe by fastforce
    thus "\<beta>\<in>K\<^sub>1" using \<open>\<alpha> \<in> \<omega>\<close> omega_lemma by blast 
  qed
  thus "succ(\<alpha>)\<in>\<omega>" using * omega_lemma by simp
  next
   fix \<alpha>::Set  assume "\<alpha>\<in>On" and **: "succ(\<alpha>)\<in>\<omega>"
   have "\<alpha>\<in>succ(\<alpha>)" using Ex4_32 Prop4_10_a Prop4_8_b \<open>\<alpha> \<in> On\<close> forall_in_def ordinal_def 
    ordinals_lemma by auto 
   moreover have "\<forall>\<beta>\<in>On. \<beta>\<in>\<alpha> \<longrightarrow> \<beta>\<in>succ(\<alpha>)" unfolding forall_in_def
    using Ex4_29_a Prop4_10_a \<open>\<alpha> \<in> On\<close> calculation ordinal_def ordinals_lemma by blast 
   thus "\<alpha>\<in>\<omega>" using "**" Prop4_8_e \<open>\<alpha> \<in> On\<close> calculation forall_in_def omega_lemma 
    ordinals_lemma by auto 
qed  
    
   
lemma Prop4_11_b: "set(\<omega>)"
sorry


(* Ioanna: page 247 *) 


lemma Prop4_11_c: "\<emptyset> \<in> X \<and> (\<forall>u. u \<in> X \<longrightarrow> succ u \<in> X) \<Longrightarrow> \<omega> \<subseteq> X"
sorry

lemma Prop4_11_d: "\<forall>\<alpha>.(\<alpha> \<in> \<omega> \<and> \<beta> <\<^sub>o \<alpha>) \<longrightarrow> \<beta> \<in> \<omega>"
sorry

text{* \begin{quote}
          The elements of $\omega$ are called finite ordinals. We shall use the standard
          notation: 1 for 0', 2 for 1', 3 for 2', and so on. Thus,
          $0 \in \omega$, $1\in \omega$, $2 \in \omega$, $3 \in \omega$, $\dots$.
          The non-zero ordinals that are not successor ordinals are called limit ordinals. *}


definition finite_ordinal :: "Set \<Rightarrow> bool" ("(_ is a finite ordinal)" 70)
  where "n is a finite ordinal \<longleftrightarrow> (n \<in> \<omega>)"

abbreviation set_one :: Set ("\<one>")
  where "\<one> \<equiv> succ(\<emptyset>)"

abbreviation set_two :: Set ("\<two>")
  where "\<two> \<equiv> succ(\<one>)"

abbreviation set_three :: Set ("\<three>")
  where "\<three> \<equiv> succ(\<two>)"

definition limit_ord :: "Set \<Rightarrow> bool" ("Lim")
where "Lim(x) \<longleftrightarrow> (x is an ordinal) \<and> x \<notin> K1"

notation limit_ord ("(_ is a limit ordinal)" 70)

lemma Ex4_33_a: "Lim(Abs_Set \<omega>)"
sorry

lemma Ex4_33_b: "\<forall>\<alpha>\<in>On. \<forall>\<beta>\<in>On. (Lim(\<alpha>) \<and> \<beta> <\<^sub>o \<alpha>) \<longrightarrow> succ \<beta> <\<^sub>o \<alpha>"
sorry

lemma Prop4_12_a: 
  "\<forall>x::Set. x \<subseteq> On \<longrightarrow> (\<Union>x \<in> On 
                   \<and> (\<forall>\<alpha>\<in>On. (\<alpha> \<in> x \<longrightarrow> \<alpha> \<le>\<^sub>o \<Union>x)) 
                   \<and> (\<forall>\<beta>\<in>On. (\<forall>\<alpha>\<in>On. (\<alpha> \<in> x \<longrightarrow> \<alpha> \<le>\<^sub>o \<beta>)) \<longrightarrow> \<Union>x \<le>\<^sub>o \<beta>))"
(* Ioa: bracketing typo at Mendelson's text. *)
proof (rule allI, rule impI, rule conjI, auto)
  fix x::Set
  assume *: "x\<subseteq>On"
  show **: "(\<Union>x) \<in> On" 
    proof -
      have 0: "the \<in>-relation well-orders (\<Union>x)" using Prop4_8_f 
        by (meson "*" Ex4_12_e Ex4_25 Ex4_29_b Prop4_8_g ordinal_def) 
      have 1: "(\<Union>x) is transitive" by (metis * Abs_Set_inverse Ex4_29_g Ex4_5 mem_Collect_eq 
                                              ordinal_def ordinals_lemma subclass'_def universe) 
      hence 2: "Ord(\<Union>x)" unfolding ordinal_def using 0 by simp
      have "(\<Union>x) is a set" by (simp add: sum_set_remark) 
      thus ?thesis unfolding ordinals_def 
        using ordinals_definable comprehensionI Prop4_8_h Prop4_8_i 2 ordinals_def by fastforce
    qed
  show "(\<forall>\<alpha>\<in>On. (\<alpha> \<in> x \<longrightarrow> \<alpha> \<le>\<^sub>o \<Union>x))" 
    unfolding forall_in_def 
  proof (rule allI, rule impI, rule impI)
    fix \<alpha>::Set
    assume "\<alpha>\<in>On" and "\<alpha>\<in>x" 
    hence 3: "\<alpha>\<subseteq>\<Union>x" using subsetI sum_class_lemma by blast 
    moreover hence "\<alpha> is an ordinal class" using \<open>\<alpha> \<in> On\<close> ordinals_lemma by blast 
    show "\<alpha> \<le>\<^sub>o \<Union>x" 
    proof (cases "\<alpha>= \<Union>x")
      assume "\<alpha> = \<Union>x" 
      thus ?thesis using ** leq_on_ordinals_def by auto
      next
      assume "\<alpha> \<noteq> \<Union>x" 
      hence "\<alpha>\<in>\<Union>x" unfolding strict_subclass_def using 3 Prop4_8_b \<open>\<alpha> is an ordinal class\<close>
        by (metis ** Abs_Set_inverse Ex4_1 Prop4_8_d mem_Collect_eq ordinals_lemma 
                  subclass'_def universe) 
      thus ?thesis unfolding leq_on_ordinals_def less_on_ordinals_def by (simp add: ** \<open>\<alpha> \<in> On\<close>) 
    qed
  qed
  show "\<forall>\<beta>\<in>On. (\<forall>\<alpha>\<in>On. (\<alpha> \<in> x \<longrightarrow> \<alpha> \<le>\<^sub>o \<beta>)) \<longrightarrow> \<Union>x \<le>\<^sub>o \<beta>" unfolding forall_in_def
  proof (rule allI, rule impI, rule impI)
    fix \<beta>::Set
    assume "\<beta>\<in>On" and 4: "(\<forall>\<alpha>::Set. (\<alpha>\<in>On) \<longrightarrow> (\<alpha> \<in> x \<longrightarrow> \<alpha> \<le>\<^sub>o \<beta>))"
    show "\<Union>x \<le>\<^sub>o \<beta>" 
    proof (cases "\<beta>=\<Union>x")
      assume "\<beta>=\<Union>x" thus ?thesis using ** leq_on_ordinals_def by auto
      next
      assume "\<beta>\<noteq>\<Union>x" 
      hence 5: "\<beta>\<in>\<Union>x \<or> \<Union>x\<in>\<beta>" by (metis ** Abs_Set_inverse Ex4_5 Prop4_8_d \<open>\<beta> \<in> On\<close>   
                                    mem_Collect_eq ordinals_lemma universe) 
      have "\<Union>x\<in>\<beta>" 
      proof (rule ccontr)
        assume "\<Union>x\<notin>\<beta>" 
        hence "\<beta>\<in>\<Union>x" using 5 ** by simp
        then obtain \<gamma> where 6: "set(\<gamma>) \<and> \<gamma>\<in>x \<and> \<beta>\<in>\<gamma>" using sum_class_lemma Ex4_1 by blast
        hence "\<gamma>\<in>On" using "*" subclass'_def by blast 
        thus False using 6 4 by (metis Abs_Set_inverse Prop4_8_d leq_on_ordinals_def 
                                       less_on_ordinals_def mem_Collect_eq ordinals_lemma universe)
      qed
      thus ?thesis by (simp add: ** \<open>\<beta> \<in> On\<close> leq_on_ordinals_def less_on_ordinals_def)
    qed
  qed
qed


lemma Prop4_12_b: "\<forall>x. x \<subseteq> On \<and> x \<noteq> \<emptyset> \<and> (\<forall>\<alpha>. \<alpha> \<in> x \<longrightarrow> (\<exists>\<beta>. \<beta> \<in> x \<and> \<alpha> <\<^sub>o \<beta>)) \<longrightarrow> 
                                          Lim(Abs_Set (\<Union>x))"
sorry

(* Ioanna: page 248 *)

lemma Ex4_34_a: "\<forall>\<alpha>. succ_ord(\<alpha>) \<longrightarrow> (succ(Abs_Set (\<Union>\<alpha>)) = \<alpha>) \<and> (Lim(\<alpha>) \<longrightarrow> \<Union>\<alpha> = \<alpha>)"
sorry

lemma Ex4_34_b: "\<forall>x. x \<noteq> \<emptyset> \<and> x \<subseteq> On \<longrightarrow> (\<forall>y. y \<in> x \<longrightarrow> \<Inter>x \<le>\<^sub>o y)"
sorry

subsection{*Transfinite Induction: Second Form*}

lemma Prop4_13_a: "\<emptyset> \<in> X \<and> (\<forall>\<alpha>. (\<alpha> is an ordinal) \<longrightarrow> 
                                 (\<alpha> \<in> X \<longrightarrow> succ \<alpha> \<in> X)) 
                         \<and> (\<forall>\<alpha>. Lim(\<alpha>) \<and> (\<forall>\<beta>. \<beta> <\<^sub>o \<alpha> \<longrightarrow> \<beta> \<in> X) \<longrightarrow> \<alpha> \<in> X) \<Longrightarrow> On \<subseteq> X"
sorry

lemma Prop4_13_b: "\<delta> \<in> On \<and> \<emptyset> \<in> X \<and> (\<forall>\<alpha>. \<alpha> <\<^sub>o \<delta> \<and> \<alpha> \<in> X \<longrightarrow> succ \<alpha> \<in> X) \<and>
  (\<forall>\<alpha>. \<alpha> <\<^sub>o \<delta> \<and> Lim(\<alpha>) \<and> (\<forall>\<beta>. \<beta> <\<^sub>o \<alpha> \<longrightarrow> \<beta> \<in> X) \<longrightarrow> \<alpha> \<in> X) \<Longrightarrow> \<delta> \<subseteq> X"
sorry

lemma Prop4_13_c: "\<emptyset> \<in> X \<and> (\<forall>\<alpha>. \<alpha> <\<^sub>o \<omega> \<and> \<alpha> \<in> X \<longrightarrow> succ \<alpha> \<in> X) \<Longrightarrow> \<omega> \<subseteq> X" 
sorry

(* Ioanna: page 249 *) 

lemma Prop4_14_a: "\<forall>X::Class. (\<exists>!Y::Class. 
                    ((Y is a function) 
                    \<and> (dom(Y) = On) 
                    \<and> (\<forall>\<alpha>::Set. ((\<alpha> is an ordinal) \<longrightarrow> (Y\<acute>\<alpha> = X\<acute>(Y\<restriction>\<alpha>))))))"

sorry


lemma Prop4_14_b: "\<forall>x::Set.\<forall>X\<^sub>1 X\<^sub>2::Class.\<exists>!Y::Class.
                    ((Y is a function)
                    \<and> (dom(Y) = On)
                    \<and> (Y\<acute>\<emptyset> = x)
                    \<and> (\<forall>\<alpha>::Set. (\<alpha> is an ordinal) \<longrightarrow> (Y\<acute>(succ(\<alpha>)) = X\<^sub>1\<acute>(Y\<acute>\<alpha>)))
                    \<and> (\<forall>\<alpha>::Set. Lim(\<alpha>) \<longrightarrow> (Y\<acute>\<alpha> = X\<^sub>2\<acute>(Y \<inter> (\<alpha> \<times> \<V>)))))"
sorry

lemma Prop4_14_c: 
    fixes \<delta>::Set
    assumes "\<delta> is an ordinal"
    shows "\<forall>x::Set. \<forall>X\<^sub>1 X\<^sub>2::Class. \<exists>!Y::Class. 
            ((Y is a function) 
             \<and> (dom(Y) = \<delta>)
             \<and> ((Y\<acute>\<emptyset>) = x)
             \<and> (\<forall>\<alpha>\<in>On.(succ(\<alpha>) <\<^sub>o \<delta>) \<longrightarrow> (Y\<acute>(succ(\<alpha>)) = X\<^sub>1\<acute>(Y\<acute>\<alpha>)))
             \<and> (\<forall>\<alpha>\<in>On.(Lim(\<alpha>) \<and> (\<alpha> <\<^sub>o \<delta>)) \<longrightarrow> (Y\<acute>\<alpha> = X\<^sub>2\<acute>(Y\<restriction>\<alpha>))))"
text{* The following proof is much longer than Mendelsons:
       \begin{quote}
       [...] and part (c) follows from (b).
       \end{quote} *}
proof (rule allI, rule allI, rule allI, rule ex1I)
  fix x::Set
  fix X\<^sub>1 X\<^sub>2::Class
  have "\<exists>Y::Class. ((Y is a function) \<and> (dom(Y) = \<delta>) \<and> (Y\<acute>\<emptyset> = x)
             \<and> (\<forall>\<alpha>\<in>On.(succ(\<alpha>) <\<^sub>o \<delta>) \<longrightarrow> (Y\<acute>(succ(\<alpha>)) = X\<^sub>1\<acute>(Y\<acute>\<alpha>)))
             \<and> (\<forall>\<alpha>\<in>On.(Lim(\<alpha>) \<and> \<alpha> <\<^sub>o \<delta>) \<longrightarrow> Y\<acute>\<alpha> = X\<^sub>2\<acute>(Y\<restriction>\<alpha>)))"
  proof -
    obtain Y'::Class where Y': "(Y' is a function)  \<and> dom(Y') = On  \<and> Y'\<acute>\<emptyset> = x 
                            \<and> (\<forall>\<alpha>::Set. (\<alpha> is an ordinal) \<longrightarrow> (Y'\<acute>succ(\<alpha>) = X\<^sub>1\<acute>(Y'\<acute>\<alpha>)))
                            \<and> (\<forall>\<alpha>::Set. Lim(\<alpha>) \<longrightarrow> Y'\<acute>\<alpha> = X\<^sub>2\<acute>(Y'\<restriction>\<alpha>))" 
      using Prop4_14_b unfolding restriction_def by blast 
    def Y == "Y'\<restriction>\<delta>"
    hence *: "(Y is a function)  \<and> dom(Y) = On  \<and> Y\<acute>\<emptyset> = x 
              \<and> (\<forall>\<alpha>::Set. (\<alpha> is an ordinal) \<longrightarrow> (Y\<acute>succ(\<alpha>) = X\<^sub>1\<acute>(Y\<acute>\<alpha>)))
              \<and> (\<forall>\<alpha>::Set. Lim(\<alpha>) \<longrightarrow> Y\<acute>\<alpha> = X\<^sub>2\<acute>(Y\<restriction>\<alpha>))"  sorry
    thus ?thesis by (metis Ex4_17_b Prop4_8_d Prop4_8_g Transitive_def Y' Y_def assms ordinal_def 
                           ordinal_number_def ordinals_lemma) 
  qed
  oops

(* Add example 1: ordinal addition *)

(* page 250 *)

consts ordinal_addition :: "Set \<Rightarrow> Set \<Rightarrow> Set" (infix "+\<^sub>o" 80)
       ordinal_multiplication :: "Set \<Rightarrow> Set \<Rightarrow> Set" (infix "\<times>\<^sub>o" 80)

(* Add example 2: ordinal multiplication, and exercises 4.35, 4.36, and the notation in the
   footnote. *)

abbreviation mem_rel_restr:: "Class \<Rightarrow> Class" ("(\<E>\<downharpoonright>_)")
where "\<E>\<downharpoonright>X \<equiv> {x::Set \<bar> (\<exists> u v::Set. (x = \<langle>u,v\<rangle> \<and> u \<in> v \<and> u \<in> X \<and> v \<in> X)) }"
(* How can we remove the space between \<E> and \<^sub>X without creating a parse error? *) 


lemma mem_rel_restr_lemma: "\<forall>X. x \<in> (\<E>\<downharpoonright>X) \<longleftrightarrow> (\<exists>u v. x = \<langle>u,v\<rangle> \<and> u \<in> v \<and> u \<in> X \<and> v \<in> X)"
(* The following proof does not work any more:
using Ex4_30_a Ex4_5 Ex_4_23 less_on_ordinals_def less_on_ordinals_remark1 universe *)
sorry

(* page 251 *)
text{* \begin{quote}
       From this point on, we shall express many theorems of NBG in English by
       using the corresponding informal English translations. This is done to avoid writing
       lengthy wfs that are difficult to decipher and only in cases where the reader should be
       able to produce from the English version the precise wf of NBG.
       \end{quote} 

       So from now on we shall add the English statements of the theorems as well, to ease the 
       process of writing controlled natural language parsers later.*}

lemma Prop4_15: 
    fixes R Y F::Class
  assumes "R is a well-ordering of Y"  --"Let R be a well-ordering relation on a class Y;"
      and "F is a function from Y to Y" --"Let F be a function from Y into Y"
      and "\<forall>u v. u \<in> Y \<and> v \<in> Y \<and> \<langle>u,v\<rangle> \<in> R \<longrightarrow> \<langle>F\<acute>u,F\<acute>v\<rangle> \<in> R"
      --"such that, for any u and v in Y, if \<langle>u, v\<rangle>\<in> R, then \<langle>F\<acute>u,F\<acute>v\<rangle> \<in> R."
    shows "(\<forall>u. u \<in> Y \<longrightarrow> (u = F\<acute>u \<or> \<langle>u,F\<acute>u\<rangle> \<in> R))" 
    --"Then, for all u in Y, u = F\<acute>u  or \<langle>u,F\<acute>u\<rangle> \<in> R)."
text{* \begin{quote}
       Let $R$ be a well-ordering relation on a class $Y$; that is, $R We Y$. Let $F$ be a
       function from $Y$ into $Y$ such that, for any $u$ and $v$ in $Y$, if $(u, v) \in R$, then
       $(F'u,F'v) \in R$. Then, for all $u$ in $Y$, $u = F'u$ or $(u,F'u) \in R$.
       \end{quote} *}
proof -
  def X \<equiv> "{u \<bar> \<langle>F\<acute>u, u\<rangle> \<in> R}"  --"Let X = {u \<bar> (F\<acute>u, u) \<in> R}."
  have "X = \<emptyset>"  --"We wish to show that X=0." 
  proof (rule ccontr)
    assume "X\<noteq>\<emptyset>" --"Assume \<open>X \<noteq> \<emptyset>\<close>." 
    from assms(1) have "X\<subset>Y" and "R We Y" unfolding Well_ord_of_def X_def  sorry
  --"Since X \<subset> Y and R well-orders Y,"
    obtain u where "(u \<in> X) \<and> (\<forall>v::Set. (v\<in>X \<longrightarrow> (\<langle>u, v\<rangle> \<in> R)))" 
      using empty_set mem_rel_restr_lemma one_in_omega sorry
      --"there is an R-least element \<open>u\<^sub>0\<close> of X." 
    hence *: "\<langle>F\<acute>u, u\<rangle> \<in> R" using X_def comprehensionE by blast  --"Hence, \<open>(F'u\<^sub>0 , u\<^sub>0) \<in> R\<close>." 
    hence "\<langle>F\<acute>(F\<acute>u), F\<acute>u\<rangle> \<in> R" sorry
      --"Therefore \<open>(F'(F'u\<^sub>0), F'u\<^sub>0) \<in> R\<close>."
    hence "F\<acute>u \<in> X" sorry --"Thus, \<open>F'u\<^sub>0 \<in> X\<close>,"
    have "\<langle>F\<acute>u, u\<rangle>\<in>R" using * by simp --"but \<open>F'u\<^sub>0\<close> is R-smaller than \<open>u\<^sub>0\<close>,"
    thus False using empty_set mem_rel_restr_lemma sorry 
      --"contradicting the definition of \<open>u\<^sub>0\<close>."
  qed 
  thus ?thesis using empty_set mem_rel_restr_lemma sorry 
qed

text{* The definition below was originally hidden in the statement of Corollary 4.16, 
       which follows.*}

(* Are the first two parts of the defining formula below necessary? *)
definition increasing_on :: "Class \<Rightarrow> Class \<Rightarrow> bool" ("(_ is increasing on _)" 70)
  where "(F is increasing on Y) \<longleftrightarrow> (Y \<subseteq> On)  
                                    \<and> (F: Y \<rightarrow> Y)
                                    \<and> (\<forall>\<alpha> \<beta>. \<alpha> \<in> Y \<and> \<beta> \<in> Y \<and> \<alpha> <\<^sub>o \<beta> \<longrightarrow> (F\<acute>\<alpha>) <\<^sub>o (F\<acute>\<beta>))"

lemma Cor4_16: 
    fixes Y F :: Class
  assumes "Y \<subseteq> On"
      and "F: Y \<rightarrow> Y"
      and "(\<forall>\<alpha> \<beta>. \<alpha> \<in> Y \<and> \<beta> \<in> Y \<and> \<alpha> <\<^sub>o \<beta> \<longrightarrow> (F\<acute>\<alpha>) <\<^sub>o (F\<acute>\<beta>))"
    shows "(\<forall>\<alpha>. \<alpha> \<in> Y \<longrightarrow> (\<alpha> \<le>\<^sub>o (F\<acute>\<alpha>)))"
text{* \begin{quote}
       If $Y$ is a class of ordinals, $F: Y \rightarrow Y$, and $F$ is increasing on $Y$ 
       (that is, $a \in Y \land \beta \in Y \land a <_o \beta \Rightarrow 
       F\prime\alpha <_o F\prime\beta$), then $a\leq_o F\prime\alpha$ for all $\alpha$ in $Y$.
       \end{quote} *}
using Prop4_15[where R="\<E>\<downharpoonright>Y"] Prop4_8_f Ex4_25 sorry

--"Proof. In Proposition 4.15, let R be \<open>\<E>\<downharpoonright>Y\<close>. Note that \<open>\<E>\<downharpoonright>y\<close> well-orders Y, by Proposition
4.8(f) and Exercise 4.25."

text{* The definition below was originally hidden in the statement of Corollary 4.17, 
       which follows.*}

abbreviation subset_of_a_segment :: "Set \<Rightarrow> Set \<Rightarrow> bool" ("(_ is a subset of a segment of _)" 70)
  where "(y is a subset of a segment of \<beta>) \<equiv> \<exists>\<alpha>::Set. (\<alpha> <\<^sub>o \<beta>) \<and> (y \<subseteq> \<alpha>)"

lemma Cor4_17: 
  assumes "\<alpha> <\<^sub>o \<beta>"
      and "y \<subseteq> \<alpha>" 
    shows "\<langle>Abs_Set(\<E>\<downharpoonright>\<beta>) , \<beta>\<rangle> and \<langle>Abs_Set(\<E>\<downharpoonright>y) , y\<rangle> are not similar"

text{* \begin{quote}
       Let "\alpha <_o \beta$ and $y\subseteq\alpha$; that is, let $y$ be a subset of a segment 
       of $\beta$. Then $\langle\mathcal{E}_\beta, \beta\rangle$ is not similar to 
       $\langle\mathcal{E}_y, y\rangle *}

proof (rule ccontr)
text{* Somehow Isabelle can not deal with assuming similarity below, instead of the double
       negation statement that we ended up using. Which rule would allow assuming similarity
       instead of not not similarity? *}
  assume "\<not>(\<langle>Abs_Set(\<E>\<downharpoonright>\<beta>) , \<beta>\<rangle> and \<langle>Abs_Set(\<E>\<downharpoonright>y) , y\<rangle> are not similar)" 
    --"Assume \<open>\<langle>\<E>\<downharpoonright>\<beta>, \<beta>\<rangle>\<close> is similar to \<open>\<langle>\<E>\<downharpoonright>y, y\<rangle>\<close>."  
  obtain f:: Set where f: "(f is a surjection from \<beta> onto y) 
                           \<and> (\<forall>u v::Set. ((u\<in>\<beta> \<and> v\<in>\<beta>)\<longrightarrow> (u <\<^sub>o v \<longleftrightarrow> (f\<acute>u) <\<^sub>o (f\<acute>v))))"
    using empty_set assms(1) less_on_ordinals_def mem_rel_restr_lemma sorry
       --"Then there is a function f from \<beta> onto y such that, for any u and v in \<beta>, 
       \<open>u<\<^sub>o v \<longleftrightarrow> f\<acute>u <\<^sub>o f\<acute>v\<close>.)" 
  have "ran(f) = y" unfolding surjection_from_onto_def 
    using empty_set Rep_Set mem_rel_restr_lemma sorry --"Since the range of f is y,"
  hence *: "f\<acute>\<alpha> \<in> y" sorry    --"f\<acute>\<alpha> \<in> y."
  have "y\<subseteq>\<alpha>" using assms(2) by auto     --"But y\<subseteq>\<alpha>."
  hence **: "(f\<acute>\<alpha>) <\<^sub>o \<alpha>" using * less_on_ordinals_remark1 subset sorry --"Hence \<open>f\<acute>\<alpha><\<^sub>o \<alpha>\<close>."
  from Cor4_16 have "\<alpha> \<le>\<^sub>o (f\<acute>\<alpha>)"  
    sorry 
    --"But, by Corollary 4.16, \<open>\<alpha> \<le>\<^sub>o (f\<acute>\<alpha>)\<close>,"
  thus False using Prop4_10_b ** leq_on_ordinals_def 
    by (metis Prop4_8_a Transitive_def less_on_ordinals_def ordinal_def ordinals_lemma 
              subclass'_def)
      --"which yields a contradiction."
qed

(* page 252 *)

(* Ioanna: Still to do is to change the statements to something closer to Mendelson's wording
           in the following lemmas. *)
(* Ioanna: perhaps the following is necessary? *)
lemma "\<forall>\<alpha>::Set. ((\<E>\<downharpoonright>\<alpha>) is a set)" 
proof 
  fix \<alpha>::Set
  have "(\<E>\<downharpoonright>\<alpha>) \<subseteq> X\<times>X" unfolding cartesian_product_def sorry
  thus "(\<E>\<downharpoonright>\<alpha>) is a set" sorry
qed

lemma Cor4_18a: "\<forall>\<alpha> \<beta>::Set. ((\<alpha> is an ordinal) \<and> (\<beta> is an ordinal))\<longrightarrow> 
                            ((\<alpha> \<in> On \<and> \<beta> \<in> On \<and> \<alpha> \<noteq> \<beta>) \<longrightarrow> 
                             \<not> (Sim \<langle>Abs_Set(\<E>\<downharpoonright>(Rep_Set \<alpha>)),\<alpha>\<rangle> \<langle>Abs_Set(\<E>\<downharpoonright>\<beta>),\<beta>\<rangle>))"
sorry

lemma Cor4_18b: "\<forall>\<alpha> f::Set. (\<alpha> is an ordinal \<and> Simp f \<langle>Abs_Set(\<E>\<downharpoonright>\<alpha>),\<alpha>\<rangle> \<langle>Abs_Set(\<E>\<downharpoonright>\<alpha>),\<alpha>\<rangle>) \<longrightarrow> 
                            (\<forall>\<beta>. \<beta> <\<^sub>o \<alpha> \<longrightarrow> f\<acute>\<beta> = \<beta>)"
sorry

lemma Prop4_19:
    fixes u r::Set
  assumes "u \<noteq> \<emptyset>"
      and "u = the field of r" 
      and "r is a wellorder"
    shows "\<exists>!\<gamma> f::Set. (\<gamma> is an ordinal) \<and> (Simp f \<langle>Abs_Set(\<E>\<downharpoonright>\<gamma>),\<gamma>\<rangle> \<langle>r,u\<rangle>)"
sorry

(* page 253 *)

lemma Ex4_37: 
    fixes r::Set
  assumes "\<emptyset>  =the field of r" 
      and "r is a wellorder"
    shows "\<exists>!\<gamma> f::Set. (\<gamma> is an ordinal) \<and> (Simp f \<langle>Abs_Set(\<E>\<downharpoonright>\<gamma>),\<gamma>\<rangle> \<langle>r,u\<rangle>)"
      and "\<forall>\<gamma>::Set. \<exists>! f::Set. ((\<gamma> is an ordinal) \<and> (Simp f \<langle>Abs_Set(\<E>\<downharpoonright>\<gamma>),\<gamma>\<rangle> \<langle>r,u\<rangle>))
                               \<longrightarrow> (\<gamma>=\<emptyset>)"  
sorry

lemma Prop4_20: "\<forall>R X::Class.
                  (R We X
                  \<and> Pr(X)
                  \<and> (\<forall>y. y \<in> X \<longrightarrow> set(Seg R X y)))
                    \<longrightarrow> ((\<exists>!H.
                          Fnc1(H)
                          \<and> (H: On \<rightarrow> X)
                          \<and> (\<forall>\<alpha> \<beta>. \<alpha> \<in> On \<and> \<beta> \<in> On \<longrightarrow> (\<alpha> \<in> \<beta> \<longleftrightarrow> \<langle>H\<acute>\<alpha>,H\<acute>\<beta>\<rangle> \<in> R))))"
sorry

lemma Ex4_38: 
  fixes X::Class
  assumes "(Pr(X) \<and> X \<subseteq> On)" --"Perhaps we should add an abbreviation for this."
  shows "\<exists>!H::Class. (H is a 1-1 function)
                     \<and> (H: On \<rightarrow> X)
                     \<and> (\<forall>\<alpha>\<in>On. \<forall>\<beta>\<in>On. (\<alpha> \<in> \<beta> \<longleftrightarrow> H\<acute>\<alpha> \<in> H\<acute>\<beta>))"
text{* \begin{quote}
       Show that, if $X$ is a proper class of ordinal numbers, then there is a
       unique one-one mapping $H$ of $On$ onto $X$ such that $\alpha\in\beta 
       \Leftrightarrow H\acute\alpha\in H\acute\beta$.
       \end{quote}
       Hint: Send 0 to the $\in$-least element of X, 1 to the second, and so on. If there were
       a last element of X, X would be a set. *}
oops

end
