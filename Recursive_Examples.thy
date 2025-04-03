theory Recursive_Examples
  imports Recursive
begin

typedecl ('e, 's) "action"

axiomatization where
  action_complete_lattice: "OFCLASS(('e, 's) action, complete_lattice_class)"

instance "action" :: (type, type) complete_lattice
  by (fact action_complete_lattice)

axiomatization
  cdo :: "'e \<Rightarrow> ('e, 's) action" and
  cseq :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" (infixr ";;" 85)
  where
  cseq_mono [mono_rule]: "\<lbrakk> P \<le> P'; Q \<le> Q' \<rbrakk> \<Longrightarrow> P ;; Q \<le> P' ;; Q'"

datatype ev = tick | view nat

recursive CountUp :: "nat \<Rightarrow> nat \<Rightarrow> _" 
  and View :: "nat \<Rightarrow> (ev, unit) action"
  and CountDown :: "nat \<Rightarrow> (ev, unit) action" where
"CountUp m n = cdo(tick) ;; View(m) ;; CountDown(n + 1)" |
"View(n) = cdo(view n)" |
"CountDown(n) = cdo(tick) ;; View(n) ;; CountUp 0 (n - 1)"

thm CountUp_unfold
thm CountDown_unfold
thm View_unfold

recursive P :: "int \<Rightarrow> bool" and Q :: "int \<Rightarrow> bool" where
"P n = Q(n + 1)" |
"Q(n) = P(n - 1)"

end