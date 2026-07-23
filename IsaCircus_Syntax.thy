section \<open> Abstract Syntax for IsaCircus \<close>

theory IsaCircus_Syntax
  imports "Abstract_Prog_Syntax.Abstract_Prog_Syntax" "Z_Toolkit.Z_Toolkit" "Channels_Events"
begin

subsection \<open> Introduction \<close>

text \<open> This theory introduces an abstract syntax tree for Circus that is suitable for 
  shallow embeddings developed using Isabelle/UTP and related tools. The approach is
  to create polymorphic constants for each Circus constructor, which can later
  be instantiated with concrete types. Each constant also has one or more accompanying
  syntactic constants and syntax translations, which give the mixfix notation for Circus
  actions and processes. A concrete language can implement the syntax by overloading
  the polymorphic constants using @{command adhoc_overloading}. Replicated operators
  are handled generically by folding the corresponding binary operator. \<close>

subsection \<open> Disable unwanted syntax \<close>

bundle Circus_Syntax
begin

unbundle Expression_Syntax

no_notation disj (infixr "|" 30)
no_notation conj (infixr "&" 35)
no_notation funcset (infixr "\<rightarrow>" 60)

no_syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /\<mapsto>/ _")
  ""         :: "maplet \<Rightarrow> updbind"              ("_")
  ""         :: "maplet \<Rightarrow> maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] \<Rightarrow> maplets" ("_,/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"           ("(1[_])")

end

subsection \<open> Abstract Constants \<close>

type_synonym ('a, 'e) channel = "'a \<Longrightarrow>\<^sub>\<triangle> 'e"

consts
  Spec         :: "('a \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 'action"
  Skip         :: "'action" ("Skip")
  Stop         :: "'action" ("Stop")
  Chaos        :: "'action" ("Chaos")
  Guard        :: "(bool, 's) expr \<Rightarrow> 'action \<Rightarrow> 'action"
  Assume       :: "(bool, 's) expr \<Rightarrow> 'action"
  InputPrefix  :: "('a, 'e) channel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> 'action)) \<Rightarrow> 'action"
  OutputPrefix :: "('a, 'e) channel \<Rightarrow> ('a, 's) expr \<Rightarrow> 'action \<Rightarrow> 'action"
  SyncPrefix   :: "(unit, 'e) channel \<Rightarrow> 'action \<Rightarrow> 'action"
  ExtChoice    :: "'action \<Rightarrow> 'action \<Rightarrow> 'action" (infixl "\<box>" 58)
  ExtChoiceIdx :: "'i set \<Rightarrow> ('i \<Rightarrow> 'action) \<Rightarrow> 'action"
  Rename       :: "('e \<leftrightarrow> 'f) \<Rightarrow> 'action \<Rightarrow> 'action"
  Hide         :: "'action \<Rightarrow> 'e set \<Rightarrow> 'action"
  ParallelAct  :: "('a \<Longrightarrow> 's) \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> 'e set \<Rightarrow> 'action \<Rightarrow> 'action \<Rightarrow> 'action" (infixl "\<lbrakk>_|_|_\<rbrakk>" 58)
  Parallel     :: "'e set \<Rightarrow> 'action \<Rightarrow> 'action \<Rightarrow> 'action" (infixl "\<lbrakk>_\<rbrakk>" 58)
  Interrupt    :: "'action \<Rightarrow> 'action \<Rightarrow> 'action" (infixl "\<triangle>" 57)

text \<open> Higher-order replication over a finite set \<close>

definition Replicate :: "('action \<Rightarrow> 'action \<Rightarrow> 'action) \<Rightarrow> 'action \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'action) \<Rightarrow> 'action" where
"Replicate Op U I P = Finite_Set.fold Op U (P ` I)"

subsection \<open> Syntax Translations \<close>

syntax 
  "_Spec"           :: "svids \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_:[_,_]" [100,0,0] 100)
  "_Guard"          :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>& _" [59, 60] 60)
  "_InputPrefix"    :: "chan \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("(3(_)\<^bold>?(_) /\<rightarrow> _)" [59, 0, 60] 60)
  \<comment> \<open> Bounded Prefix \<close>
  "_InputBPrefix"   :: "chan \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3(_)\<^bold>?(_)\<in>(_) /\<rightarrow> _)" [59, 0, 0, 60] 60)
  \<comment> \<open> Constrained Prefix \<close>
  "_InputCPrefix"   :: "chan \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3(_)\<^bold>?(_) | (_) /\<rightarrow> _)" [59, 0, 0, 60] 60)
  \<comment> \<open> Bounded and Constrained Prefix \<close>
  "_InputBCPrefix"  :: "chan \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3(_)\<^bold>?(_)\<in>(_) /| (_) /\<rightarrow> _)" [59, 0, 0, 0, 60] 60)
  "_OutputPrefix"   :: "chan \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3(_)\<^bold>!(_) /\<rightarrow> _)" [59, 0, 60] 60)
  "_SyncPrefix"     :: "chan \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow> _" [59, 60] 60)
  "_Interleave"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<interleave>" 58)
  "_InterleaveAct"  :: "logic \<Rightarrow> svids \<Rightarrow> svids \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk>_|_\<rbrakk> _" [58, 0, 0, 59] 58)
  "_Hide"           :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<Zhide> _" [60, 61] 61)
  "_Rename"         :: "logic \<Rightarrow> rnenum \<Rightarrow> logic" ("_ [_]" [60, 0] 61)
  "_ExtChoiceIdx"   :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<box>_/\<in>_. _" [0, 0, 10] 10)
  "_InterleaveIter" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<interleave>_/\<in> _. _" [0, 0, 10] 10)
  "_SequentialIter" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (";;_/\<in>_. _" [0, 0, 10] 10)
  "_ParallelIter"   :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrakk>_\<rbrakk>_/\<in>_. _" [0, 0, 10] 10)

translations 
  "_Spec a p q"                \<rightleftharpoons> "CONST Spec a (p)\<^sub>e (q)\<^sub>e"
  "_Guard b P"                 \<rightleftharpoons> "CONST Guard (b)\<^sub>e P"
  "_InputPrefix c x P"         \<rightleftharpoons> "CONST InputPrefix c (CONST UNIV) (\<lambda> x. ((CONST True)\<^sub>e, P))"
  "_InputBPrefix c x A P"      \<rightleftharpoons> "CONST InputPrefix c A (\<lambda> x. ((CONST True)\<^sub>e, P))"
  "_InputCPrefix c x B P"      \<rightleftharpoons> "CONST InputPrefix c (CONST UNIV) (\<lambda> x. ((B)\<^sub>e, P))"
  "_InputBCPrefix c x A B P"   \<rightleftharpoons> "CONST InputPrefix c A (\<lambda> x. ((B)\<^sub>e, P))"
  "_OutputPrefix c e P"        \<rightleftharpoons> "CONST OutputPrefix c (e)\<^sub>e P"
  "_SyncPrefix c P"            \<rightleftharpoons> "CONST SyncPrefix c P"
  "_Interleave"                \<rightleftharpoons> "CONST Parallel {}"
  "_InterleaveAct P ns1 ns2 Q" \<rightleftharpoons> "CONST ParallelAct ns1 ns2 {} P Q"
  "_Hide P A"                  \<rightleftharpoons> "CONST Hide P A"
  "_Rename P f"                \<rightleftharpoons> "CONST Rename P f"
  "_ExtChoiceIdx x A P"        \<rightleftharpoons> "CONST ExtChoiceIdx A (\<lambda> x. P)"
  "_InterleaveIter x I P"      \<rightleftharpoons> "CONST Replicate (CONST Parallel {}) Skip I (\<lambda> x. P)"
  "_SequentialIter x I P"      \<rightleftharpoons> "CONST Replicate (CONST useq) Skip I (\<lambda> x. P)"
  "_ParallelIter A x I P"      \<rightleftharpoons> "CONST Replicate (CONST Parallel A) Skip I (\<lambda> x. P)"

syntax_consts 
  "_Spec" \<rightleftharpoons> Spec and
  "_Guard" \<rightleftharpoons> Guard and
  "_InputPrefix" \<rightleftharpoons> InputPrefix and 
  "_InputBPrefix" \<rightleftharpoons> InputPrefix and
  "_InputCPrefix" \<rightleftharpoons> InputPrefix and
  "_InputBCPrefix" \<rightleftharpoons> InputPrefix and
  "_OutputPrefix" \<rightleftharpoons> OutputPrefix and
  "_SyncPrefix" \<rightleftharpoons> SyncPrefix and
  "_Interleave" \<rightleftharpoons> Parallel and
  "_InterleaveAct" \<rightleftharpoons> ParallelAct and
  "_Hide" \<rightleftharpoons> Hide and
  "_Rename" \<rightleftharpoons> Rename and
  "_ExtChoiceIdx" \<rightleftharpoons> ExtChoiceIdx and
  "_InterleaveIter" \<rightleftharpoons> Parallel and
  "_SequentialIter" \<rightleftharpoons> useq and
  "_ParallelIter" \<rightleftharpoons> Parallel

unbundle Circus_Syntax

end