section \<open> General Recursive Definitions using Complete Lattices \<close>

theory Recursive
  imports "HOL-Library.Product_Order" "HOL-Eisbach.Eisbach"
  keywords "recursive" :: "thy_defn"
begin

named_theorems recursive_defs and rec_sys_defs and mono_rule

(* Method to prove monotonicity of definitional recursive functions *)

method mono_prover = ((unfold rec_sys_defs)?, rule monoI, simp add: le_fun_def less_eq_prod_def case_prod_unfold mono_rule)

(* Method to prove equations for recursive definitions *)

method recursive_equation_prover =
  (unfold recursive_defs, subst lfp_unfold, simp add: mono_rule, simp add: rec_sys_defs prod.case_eq_if)

ML \<open> 
structure Recursive_Def =
struct

(* Assign types in a table to free variables *)

fun assign_Free_type (Free (n, t)) m = 
  if Symtab.defined m n then Free (n, the (Symtab.lookup m n)) else Free (n, t) |
assign_Free_type (f $ e) m = assign_Free_type f m $ assign_Free_type e m |
assign_Free_type (Abs (x, ty, t)) m = Abs (x, ty, assign_Free_type t m) |
assign_Free_type t _ = t

(* Extract the constant name, target type, and lambda term from an equation *)
fun rec_eq ctx recmap eq_term =
  let open Syntax; open HOLogic
      val enriched_term = check_term ctx (assign_Free_type (Type.strip_constraints (parse_term ctx eq_term)) recmap)
      val ((name, params), rhs) 
        = case enriched_term of
          Const ("HOL.eq", _) $ lhs $ rhs => (strip_comb lhs, rhs) |
          _ => error "Non-equation given in recursive definition"
      val (ident, constT) = case name of
                            Free (n, t) => (n, t) |
                            _ => error "Each equation must have a free variable at the head"
  in 
    ((ident, constT), List.foldr (fn (x, y) => HOLogic.tupled_lambda x y) rhs params)
end

fun tuple_proj n i t =
  let open HOLogic; open Syntax in 
    if n = 1 then t
    else if n = 2 then (if i = 0 then const @{const_name fst} $ t else const @{const_name snd} $ t)
    else (if i = 0 then const @{const_name fst} $ t else tuple_proj (n - 1) (i - 1) (const @{const_name snd} $ t)) 
  end;

fun mono_proof rec_fun ctx =
  let open Simplifier; open Syntax; open HOLogic in
      Goal.prove ctx [] []
      (hd (Type_Infer_Context.infer_types ctx [mk_Trueprop (const @{const_abbrev mono} $ rec_fun)]))
      (fn {context = _, prems = _}
          => (fn ctx => NO_CONTEXT_TACTIC ctx (Method_Closure.apply_method ctx @{method mono_prover} [] [] [] ctx [])) ctx)
  end;

fun rec_unfold_proof ctx (n, rec_eq) =
  let open Simplifier; open Syntax; open HOLogic; open Local_Theory
      val thm = Goal.prove ctx (Term.add_free_names rec_eq []) []
                 (hd (Type_Infer_Context.infer_types ctx [mk_Trueprop rec_eq]))
                 (fn {context = _, prems = _}
                  => (fn _ => NO_CONTEXT_TACTIC ctx (Method_Closure.apply_method ctx @{method recursive_equation_prover} [] [] [] ctx [])) ctx);
      val ctx1 = snd (note ((Binding.name (n ^ "_unfold"), []), [thm]) ctx)
  in ctx1
  end;

(* Make a set of recursive definitions, based on set of declarations and equations *)

(* FIXME: Check whether names in declarations and equations are consistent. Extract names from equations, instead of declaration, so the latter can be optional. *)

fun define_recursive (raw_rec_decls, raw_rec_eqs) ctx = 
  let open Syntax; open HOLogic; open Logic; open Specification; open Local_Theory
      val _ = if length raw_rec_decls > length raw_rec_eqs 
              then error "More declarations than equations in recursive definition" 
              else true
      val ctx' = snd (Local_Theory.begin_nested ctx)
      (* FIXME: Allow a different fixed-point operator (e.g. gfp) to be provided; will need to adapt the proof as well. *)
      val lfp = const @{const_name lfp}
      val rec_decls = map (fn (n, ty) => (n, parse_typ ctx' ty)) raw_rec_decls
      val rec_map = Symtab.make rec_decls
      val rec_funs = map (rec_eq ctx' rec_map) raw_rec_eqs
      val fst_recn = fst (fst (hd rec_funs)) 
      val recfunn = fst_recn ^ "_rec_fun"
      val recs = mk_tuple (map snd rec_funs)
      val ps = mk_tuple (map (Free o fst) rec_funs)
      val rec_fun = tupled_lambda ps recs
      fun def ctx (n, eq) atts = definition (SOME (Binding.name n, NONE, NoSyn)) [] [] ((Binding.name (n ^ "_def"), atts), eq) ctx
      val ((recfun_term, _), ctx0) = def ctx' (recfunn, Syntax.check_term ctx' (mk_equals (Free (recfunn, dummyT), rec_fun))) @{attributes [rec_sys_defs]}
      val rec_nms = map (fn (n, i) => (n, mk_equals (Free (n, dummyT), tuple_proj (length rec_funs) i (check_term ctx0 (lfp $ recfun_term))))) (ListPair.zip (map (fst o fst) rec_funs, 0 upto (length rec_funs - 1)))
      val monothm = mono_proof recfun_term ctx0
      val ctx1 = snd (note ((Binding.name ("mono_" ^ recfunn), @{attributes [mono_rule]}), [monothm]) ctx0)
      val ctx2 = Local_Theory.end_nested (fold (fn eq => fn ctx' => snd (def ctx' eq @{attributes [recursive_defs]})) rec_nms ctx1)
      val rec_eqs = map (read_term ctx2) raw_rec_eqs
      val ctx3 = fold (fn (n, rec_eq) => fn ctx' => rec_unfold_proof ctx' (n, rec_eq)) (ListPair.zip (map fst rec_decls, rec_eqs)) ctx2
  in
    ctx3
  end;
end;

Outer_Syntax.command
  @{command_keyword recursive}
  "definitions through general recursive equations over complex lattices" 
  ((Scan.optional (((Parse.name -- (Parse.$$$ "::" |-- Parse.typ)) 
                     -- Scan.repeat (@{keyword "and"} |-- (Parse.name -- (Parse.$$$ "::" |-- Parse.typ)))) >> (fn (x, xs) => x :: xs)) [] -- 
  (@{keyword "where"} |-- Parse.enum1 "|" Parse.term))
   >> (Toplevel.local_theory NONE NONE o Recursive_Def.define_recursive)) 

\<close>

end