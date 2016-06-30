theory remove_notation
imports Main 
begin

(* delete all notations we want to redefine *)
no_notation  subset  ("op <") and
  subset  ("(_/ < _)" [51, 51] 50) and
  subset_eq  ("op <=") and
  subset_eq  ("(_/ <= _)" [51, 51] 50) and
  subset  ("op \<subset>") and
  subset  ("(_/ \<subset> _)" [51, 51] 50) and
  subset_eq  ("op \<subseteq>") and
  subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) and
  Set.member  ("op :") and
  Set.member  ("(_/ : _)" [51, 51] 50) and
  Set.not_member  ("op ~:") and
  Set.not_member  ("(_/ ~: _)" [51, 51] 50) and
  Set.member      ("op \<in>") and
  Set.member      ("(_/ \<in> _)" [51, 51] 50) and
  Set.not_member  ("op \<notin>") and
  Set.not_member  ("(_/ \<notin> _)" [51, 51] 50) and
  supset  ("op \<supset>") and
  supset  ("(_/ \<supset> _)" [51, 51] 50) and
  supset_eq  ("op \<supseteq>") and
  supset_eq  ("(_/ \<supseteq> _)" [51, 51] 50) and
  inter  (infixl "\<inter>" 70) and
  union  (infixl "\<union>" 65) and
  Product_Type.Times  (infixr "\<times>" 80) and 
  Complete_Lattices.Union  ("\<Union>_" [900] 900) and
  Complete_Lattices.Inter ("\<Inter>_" [900] 900) and
  Fun.comp (infixl "\<circ>" 55) and
  image (infixr "`" 90) and
  Groups_Big.comm_monoid_mult_class.Setprod  ("\<Prod>_" [1000] 999) and
  power2 ("(_\<^sup>2)" [1000] 999) and 
  power ("(_\<^bsup>_\<^esup>)" [1000] 1000)
  
(*Ioanna: do not remove natural number symbols, we need Isabelle's natural numbers for FOL:_Formulas. *)
(*  Groups.one ("1") and
  Groups.minus(infixl "-" 65) *) 

(* delete all syntax from Set *)
no_syntax 
(*  "_Coll" :: "pttrn => bool => 'a set"    ("(1{_./ _})") *)
  "_Collect" :: "pttrn => 'a set => bool => 'a set"    ("(1{_ :/ _./ _})")
  "_Collect" :: "pttrn => 'a set => bool => 'a set"    ("(1{_ \<in>/ _./ _})")
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3ALL _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3EX _:_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3EX! _:_./ _)" [0, 0, 10] 10)
  "_Bleast"     :: "id => 'a set => bool => 'a"           ("(3LEAST _:_./ _)" [0, 0, 10] 10)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3! _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3? _:_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3?! _:_./ _)" [0, 0, 10] 10)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3\<forall>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3\<exists>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3\<exists>!_\<in>_./ _)" [0, 0, 10] 10)
  "_Bleast"     :: "id => 'a set => bool => 'a"           ("(3LEAST_\<in>_./ _)" [0, 0, 10] 10)
  "_setlessAll" :: "[idt, 'a, bool] => bool"  ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] => bool"  ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] => bool"  ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] => bool"  ("(3EX _<=_./ _)" [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] => bool"  ("(3EX! _<=_./ _)" [0, 0, 10] 10)
  "_setlessAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subset>_./ _)"  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subset>_./ _)"  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subseteq>_./ _)" [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subseteq>_./ _)" [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] => bool"   ("(3\<exists>!_\<subseteq>_./ _)" [0, 0, 10] 10)
  "_setlessAll" :: "[idt, 'a, bool] => bool"   ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] => bool"   ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] => bool"   ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] => bool"   ("(3? _<=_./ _)" [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] => bool"   ("(3?! _<=_./ _)" [0, 0, 10] 10)
  "_Finset" :: "args => 'a set"    ("{(_)}") 
  "Product_Type.Times" :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set"  (infixr "\<times>" 80)
  "op \<times>" :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set"
     
end
