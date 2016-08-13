theory HO_ontological_arg
imports Main
begin

(*
"Mechanized Analysis Of a Formalization of Anselm’s Ontological Argument by Eder and Ramharter"
John Rushby

http://www.csl.sri.com/users/rushby/papers/er-ontarg.pdf


Figure 3: Higher-Order Version of the Argument in PVS

HO_ontological_arg: THEORY
BEGIN
U_beings: TYPE
x, y: VAR U_beings
re?: pred[U_beings]
P: set[ pred[U_beings] ]
F: VAR (P)
>(x, y): bool = (FORALL F: F(y) => F(x)) & (EXISTS F: F(x) AND NOT F(y))
God?(x): bool = NOT EXISTS y: y > x
ExUnd: AXIOM EXISTS x: God?(x)
Realization: AXIOM
FORALL (FF:setof[(P)]): EXISTS x: FORALL F: FF(F) = F(x)
God_re: THEOREM member(re?, P) => EXISTS x: God?(x) AND re?(x)
END HO_ontological_arg

*)

definition mygreater :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "mygreater x y \<equiv> (\<forall>F. F y \<longrightarrow> F x) \<and> (\<exists> F. F x \<and> \<not> F y)"

text\<open>Let's write down explicitly that @{term F} really is the set of all predicates.\<close>
lemma mygreater_explicit_typtes:
  "mygreater x y \<longleftrightarrow>
    (\<forall>F \<in> (UNIV :: ('a \<Rightarrow> bool) set). F y \<longrightarrow> F x) \<and> (\<exists> F \<in> (UNIV :: ('a \<Rightarrow> bool) set). F x \<and> \<not> F y)"
  by(simp add: mygreater_def)

definition God :: "'a \<Rightarrow> bool" where
  "God x \<equiv> \<not> (\<exists>y. mygreater y x)"

lemma allGod: "God x"
  unfolding God_def
  apply(simp add: mygreater_def)
  by fast

corollary "\<forall>x. God x" using allGod by blast

lemma trans: "mygreater x y \<Longrightarrow> mygreater y z \<Longrightarrow> mygreater x z"
  apply(simp add: mygreater_def)
  by meson

lemma eq: "mygreater x y \<longleftrightarrow> mygreater y x"
  apply(simp add: mygreater_def)
  by fast

lemma comparable: "mygreater x y \<Longrightarrow> False"
  by (meson God_def allGod)

lemma "\<exists>tea coffee. mygreater tea coffee \<Longrightarrow> \<forall>god. \<not> god"
  using comparable by fast







text\<open>Of course, the whole theory is just a blank abuse of the @{const mygreater} definition used
     out of context. Not to be taken seriously.\<close>
end