section \<open> Manipulating Names \<close>

theory Name_Utils
  imports Main
begin

subsection \<open> Identifiers as Strings \<close>

text \<open> Each local variable is assigned the same name as the Isabelle identifier used to introduce
  the name in the binder. For this reason, we need to convert identifiers into strings. \<close>

syntax
  "_id_string"     :: "id \<Rightarrow> string" ("IDSTR'(_')")
  "_id_literal"    :: "id \<Rightarrow> String.literal" ("IDLIT'(_')")

parse_translation \<open>
let
  fun id_string_tr [Free (full_name, _)] = HOLogic.mk_string full_name
    | id_string_tr [Const (full_name, _)] = HOLogic.mk_string full_name
    | id_string_tr _ = raise Match;
  fun id_literal_tr [Free (full_name, _)] = HOLogic.mk_literal full_name
    | id_literal_tr [Const (full_name, _)] = HOLogic.mk_literal full_name
    | id_literal_tr _ = raise Match;

in
  [(@{syntax_const "_id_string"}, K id_string_tr)
  ,(@{syntax_const "_id_literal"}, K id_literal_tr)]
end
\<close>

end
