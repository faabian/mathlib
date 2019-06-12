/-
Copyright (c) 2019 Fabian Glöckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Glöckle

Generate categories corresponding to structures.
-/

import algebra.group
import category_theory.concrete_category
open expr tactic

set_option trace.app_builder true
set_option pp.universes true
-- set_option pp.implicit true
set_option formatter.hide_full_terms false
-- set_option trace.eqn_compiler.elim_match true

universes u v w

-- replace with library functions
meta def arrow_list : expr → list expr
| (pi _ _ d b)           := d :: (arrow_list b)
| x                      := [x]

meta def codomain_type (l : list expr) : option expr := l.nth (l.length - 1)

meta def codomain_is_bound (l : list expr) : bool :=
match codomain_type l with
| some (var _) := tt
| _            := ff
end

meta def codomain_is_base (l : list expr) (base : expr) :=
match codomain_type l with
| some base := tt
| _         := ff
end

meta def codomain_is_prop (l : list expr) : bool :=
match codomain_type l with
| some (sort level.zero) := tt
| _                      := ff
end

meta def compatibility_condition (struct_name : name) (base : expr) (α β i₁ i₂ f : expr)
  (field : expr) : tactic expr :=
do t ← infer_type field,
   let field_name_str := (local_pp_name field).to_string,
   let field_name := struct_name <.> field_name_str,
   arity ← get_pi_arity t,
   let target_self := codomain_is_base (arrow_list t) base,
   let target_prop := codomain_is_prop (arrow_list t),
   let nm := λ (n : ℕ), mk_simple_name (string.append "x" (to_string n)),
   let vars := list.map
    (λ n, expr.local_const (nm n) (nm n) binder_info.implicit α)
    (list.range arity),
   let fs := list.map (λ x, some (f x)) vars,
   app₁ ← mk_mapp field_name ([some α, some i₁] ++ (list.map some vars)),
   app₂ ← mk_mapp field_name ([some β, some i₂] ++ fs),
   body_main ← if target_prop then to_expr ``(%%app₁ → %%app₂)
               else (if target_self then to_expr ``(%%f (%%app₁) = %%app₂)
                     else to_expr ``(%%app₁ = %%app₂)),
   return (expr.pis vars body_main)

meta def homomorphism_id_part (struct_name : name) (base : expr) (α i ida : expr)
  (field : expr) : tactic expr :=
do t ← infer_type field,
   let target_prop := codomain_is_prop (arrow_list t),
   let field_name_str := (local_pp_name field).to_string,
   let field_name := struct_name <.> field_name_str,
   arity ← get_pi_arity t,
   let nm := λ (n : ℕ), mk_simple_name (string.append "x" (to_string n)),
   let vars := list.map
    (λ n, expr.local_const (nm n) (nm n) binder_info.implicit α)
    (list.range arity),
   xs ← mk_app field_name ([i] ++ vars),
   let idx : expr := expr.const `id [level.zero],
   rf ← if target_prop then pure (expr.app idx xs)
        else mk_app `rfl [xs],
   return (expr.lambdas vars (rf))
   -- todo: Prop-valued

meta def nth_and_part : tactic expr → ℕ → ℕ → tactic expr :=
-- (nested and-expression) (number of and-part of interest) (num_parts) → (and-part of interest)
λ e n num_parts,
match n with
| 0     := do e' ← e,
              if num_parts = 1 then return e'
              else mk_app `and.elim_left [e']
| (m+1) := do e' ← e, nth_and_part (mk_app `and.elim_right [e']) m (num_parts - 1)
end

meta def homomorphism_comp_part (struct_name : name) (base : expr) (α β γ ia ib ic f g hf hg : expr)
  (field : expr) (field_number : ℕ) (num_fields : ℕ): tactic expr :=
do t ← infer_type field,
   let target_prop := codomain_is_prop (arrow_list t),
   let field_name_str := (local_pp_name field).to_string,
   let field_name := struct_name <.> field_name_str,
   arity ← get_pi_arity t,
   let nm := λ (n : ℕ), mk_simple_name (string.append "x" (to_string n)),
   let vars := list.map
    (λ n, expr.local_const (nm n) (nm n) binder_info.implicit α)
    (list.range arity),
   let fs := list.map (λ v, (f v)) vars,
   op ← mk_app field_name ([ia] ++ vars),
   let f_op := app f op,
   op_f ← mk_app field_name ([ib] ++ fs),
   hhf ← nth_and_part (pure hf) field_number num_fields,
   hhg ← nth_and_part (pure hg) field_number num_fields,
   let hf_vars := list.foldl (λ f x, app f x) hhf vars,
   let hg_fs := list.foldl (λ f x, app f x) hhg fs,
   proof ← (if target_prop then
              to_expr ``(implies.trans %%hf_vars %%hg_fs)
            else do congr ← mk_app `congr_arg [β, γ, f_op, op_f, g, hf_vars],
                    to_expr ``(eq.trans %%congr %%hg_fs)),
   return (expr.lambdas vars proof)
-- for any transitive target? eq, if, iff, ...

meta def add_concrete_category (x : string) : command :=
do let has_x_name := name.mk_string (string.append "has_" x) name.anonymous,
   has_x ← mk_const has_x_name,
   let compatible_name := name.mk_string (string.append x "_compatible") name.anonymous,
   let compatible_id_name := name.mk_string (string.append x "_compatible_id") name.anonymous,
   let compatible_comp_name := name.mk_string (string.append x "_compatible_comp") name.anonymous,
   let compatible : expr := expr.const compatible_name [],
   let compatible_id : expr := expr.const compatible_id_name [],
   let compatible_comp : expr := expr.const compatible_comp_name [],
   decl_type ← to_expr ``(@category_theory.concrete_category (λ (α : Type), %%has_x α) %%compatible),
   decl_body ← to_expr ``(@category_theory.concrete_category.mk (λ (α : Type), %%has_x α) %%compatible
                          %%compatible_id %%compatible_comp),
   let decl_name := name.mk_string (string.append x "_category") name.anonymous,
   add_decl $ mk_definition decl_name (collect_univ_params decl_type) decl_type decl_body

-- todo: go bundled

-- #print group  -- can we obtain the "extends monoid" information somehow, or is it inlined?

meta def get_fields (struct_name : name) : tactic (option (list expr)) :=
do env ← tactic.get_env,
   let mk_name := struct_name <.> "mk",
   let mk := exceptional.to_option $ environment.get env mk_name,
   let t := option.map declaration.type mk,
   res ← traversable.traverse tactic.mk_local_pis t,
   return (option.map prod.fst res)

meta def is_data_field (field : expr) : tactic bool :=
do t ← infer_type field,
   (is_prop t) >>= (λ x, return (bnot x))  -- ??

meta def get_data_fields (struct_name : name) : tactic (option (list expr)) :=
do fields ← get_fields struct_name,
   traversable.traverse (list.mfilter is_data_field) fields

def all_but_last {α : Type u} : list α → list α
| []        := []
| (a :: []) := []
| (a :: l)  := a :: (all_but_last l)

meta def homomorphism_type (struct_name : name) : tactic declaration :=
do fields_opt ← get_data_fields struct_name,
   fields ← fields_opt,
   let base_type := list.head fields,
   let struct_u : expr :=  expr.const struct_name [level.param `u],
   let struct_v : expr :=  expr.const struct_name [level.param `v],
   α ← mk_local' `α binder_info.implicit (sort (level.succ (level.param `u))),
   β ← mk_local' `β binder_info.implicit (sort (level.succ (level.param `v))),
   i₁ ← mk_local' `i₁ binder_info.inst_implicit (struct_u α),
   i₂ ← mk_local' `i₂ binder_info.inst_implicit (struct_v β),
   f ← mk_local' `f binder_info.default (pi `a binder_info.default α β),
   compatibilities ← (list.tail fields).mmap (compatibility_condition struct_name base_type α β i₁ i₂ f),
   and ← mk_const `and,
   let body := dite (compatibilities = list.nil) (λ h, expr.const `true [])
                (λ h, list.foldr (λ a b, and a b) (list.last compatibilities h) (all_but_last compatibilities)),
   type_main ← to_expr ``((%%α → %%β) → Prop),
   let decl_type := expr.pis [α, β, i₁, i₂] type_main,
   let decl_name := mk_simple_name (string.append struct_name.to_string "_homomorphism"),
   return (mk_definition decl_name (collect_univ_params decl_type) decl_type (expr.lambdas [α, β, i₁, i₂, f] body))

meta def add_homomorphism_type (struct_name : name) : command :=
do decl ← homomorphism_type struct_name,
   add_decl decl

meta def id_homomorphism (struct_name : name) : tactic declaration :=
do fields_opt ← get_data_fields struct_name,
   fields ← fields_opt,
   let base_type := list.head fields,
   struct ← mk_const struct_name,
   let struct : expr :=  expr.const struct_name [level.param `v],
   α ← mk_local' `α binder_info.implicit (sort (level.succ (level.param `v))),
   i ← mk_local' `i binder_info.inst_implicit (struct α),
   let ida : expr := expr.const `id [level.succ (level.param `v)],
   compatibilities ← (list.tail fields).mmap (homomorphism_id_part struct_name base_type α i ida),
   let and_intro : expr := expr.const `and.intro [],
   body ← dite (compatibilities = list.nil) (λ h, pure (expr.const `trivial []))
               (λ h, list.foldr
                      (λ a b, do a' ← a, b' ← b, (tactic.mk_app `and.intro [a', b'] ))
                      (pure (list.last compatibilities h))
                      (all_but_last (list.map pure compatibilities))),
   let hom := mk_simple_name (string.append struct_name.to_string "_homomorphism"),
   stmt ← mk_app hom [α, α, i, i, ida α],
   let decl_type := expr.pis [α, i] stmt,
   let decl_name := mk_simple_name (string.append struct_name.to_string "_id_homomorphism"),
   return (mk_definition decl_name (collect_univ_params decl_type) decl_type (expr.lambdas [α, i] body))

meta def add_id_homomorphism (struct_name : name) : command :=
do decl ← id_homomorphism struct_name,
   add_decl decl

meta def homomorphism_comp (struct_name : name) : tactic declaration :=
do fields_opt ← get_data_fields struct_name,
   fields ← fields_opt,
   let base_type := list.head fields,
   let struct_u : expr :=  expr.const struct_name [level.param `u],
   let struct_v : expr :=  expr.const struct_name [level.param `v],
   let struct_w : expr :=  expr.const struct_name [level.param `w],
   α ← mk_local' `α binder_info.implicit (sort (level.succ (level.param `u))),
   ia ← mk_local' `ia binder_info.inst_implicit (struct_u α),
   β ← mk_local' `β binder_info.implicit (sort (level.succ (level.param `v))),
   ib ← mk_local' `ib binder_info.inst_implicit (struct_v β),
   γ ← mk_local' `γ binder_info.implicit (sort (level.succ (level.param `w))),
   ic ← mk_local' `ic binder_info.inst_implicit (struct_w γ),
   f ← mk_local' `f binder_info.implicit (pi `_x binder_info.default α β),
   g ← mk_local' `g binder_info.implicit (pi `_x binder_info.default β γ),
   let hom := mk_simple_name (string.append struct_name.to_string "_homomorphism"),
   hom_f ← mk_app hom [α, β, ia, ib, f],
   hom_g ← mk_app hom [β, γ, ib, ic, g],
   hf ← mk_local' `hf binder_info.default hom_f,
   hg ← mk_local' `hg binder_info.default hom_g,
   compos ← mk_mapp `function.comp [none, none, none, g, f],
   stmt ← mk_app hom [α, γ, ia, ic, compos],
   let field_numbers := list.range fields.tail.length,
   let fields_enum := list.zip fields.tail field_numbers,
   compatibilities ← fields_enum.mmap
    (λ field_enum, homomorphism_comp_part struct_name base_type α β γ ia ib ic f g hf hg
                    field_enum.fst field_enum.snd fields_enum.length),
   let and_intro : expr := expr.const `and.intro [],
   body ← dite (compatibilities = list.nil) (λ h, pure (expr.const `trivial []))
               (λ h, list.foldr
                      (λ a b, do a' ← a, b' ← b, (tactic.mk_app `and.intro [a', b'] ))
                      (pure (list.last compatibilities h))
                      (all_but_last (list.map pure compatibilities))),

   let decl_body := expr.lambdas [α, β, γ, ia, ib, ic, f, g, hf, hg] body,
   let decl_type := expr.pis [α, β, γ, ia, ib, ic, f, g, hf, hg] stmt,
   let decl_name := mk_simple_name (string.append struct_name.to_string "_homomorphism_comp"),
   return $ declaration.thm decl_name (collect_univ_params decl_type) decl_type (task.pure decl_body)
-- for any transitive target? eq, if, iff, ...

meta def add_homomorphism_comp (struct_name : name) : command :=
do decl ← homomorphism_comp struct_name,
   add_decl decl

-- run_cmd add_homomorphism_type `ordered_ring
-- #print ordered_ring_homomorphism
-- run_cmd add_id_homomorphism `ordered_ring
-- #print ordered_ring_id_homomorphism
-- run_cmd add_homomorphism_comp `ordered_ring
-- #print ordered_ring_homomorphism_comp

meta structure structure_info :=
(structure_name   : name)
(type             : expr)
(field_names      : list name)
(field_values     : list expr)
(flat             : bool := ff)
(extend           : list string := [])

-- are the following functions already defined?
def starts_with {α : Type*} [decidable_eq α]: list α → list α → bool
| l [] := tt
| [] (h::t) := ff
| (hl::tl) (h::t) := if h = hl then starts_with tl t else ff

-- sublist for the python-style slice [n:]
def end_slice {α : Type*} (n : ℕ) (l : list α): list α := prod.snd (list.split_at n l)

def find_all {α : Type*} [decidable_eq α] (l : list α) (pattern : list α) : list ℕ :=
list.filter (λ n, starts_with (end_slice n l) pattern) (list.range l.length)

def split_aux {α : Type*} [decidable_eq α] : list ℕ → list α → ℕ → ℕ → list (list α)
| [] l offset jump      := [l]
| (hi::ti) l offset jump := (list.split_at (hi - offset) l).1 :: (split_aux ti (list.split_at jump (list.split_at (hi - offset) l).2).2 (hi + jump) jump)

def split {α : Type*} [decidable_eq α] (l : list α) (pattern : list α) : list (list α) :=
split_aux (find_all l pattern) l 0 (pattern.length)

def list.replace {α : Type*} [decidable_eq α] (l : list α) (pattern : list α) (replace_with : list α) : list α :=
list.intercalate replace_with (split l pattern)

def string.replace (pattern : string) (replace_with : string) (s : string) : string :=
list.as_string (list.replace s.to_list pattern.to_list replace_with.to_list)

-- def list.collapse_repeat {α : Type} [decidable_eq α] [inhabited α] (x : α) (l : list α) : list α :=
-- list.map prod.fst $ list.filter (λ y, ¬ (y.1 = x ∧ y.2 = x)) (list.zip l (l.tail ++ [default α]))

-- def string.collapse_repeat (x : char) (s : string) : string :=
-- list.as_string (list.collapse_repeat x s.to_list)

meta def homomorphism_structure (struct_name : name) : tactic structure_info :=
do fields_opt ← get_data_fields struct_name,
   fields ← fields_opt,
   let field_names := fields.map local_pp_name,
   let base_type := list.head fields,
   let struct_u : expr :=  expr.const struct_name [level.param `u],
   let struct_v : expr :=  expr.const struct_name [level.param `v],
   α ← mk_local' `α binder_info.implicit (sort (level.succ (level.param `u))),
   β ← mk_local' `β binder_info.implicit (sort (level.succ (level.param `v))),
   i₁ ← mk_local' `i₁ binder_info.inst_implicit (struct_u α),
   i₂ ← mk_local' `i₂ binder_info.inst_implicit (struct_v β),
   f ← mk_local' `f binder_info.default (pi `ff binder_info.default α β),
   compatibilities ← (list.tail fields).mmap (compatibility_condition struct_name base_type α β i₁ i₂ f),
   type_main ← to_expr ``(Prop),
   let struct_type := expr.pis [α, β, i₁, i₂, f] type_main,
   let struct_name := mk_simple_name (string.append struct_name.to_string "_homomorphism"),
   return ⟨struct_name, struct_type, field_names.tail, compatibilities, ff, []⟩

meta def pp_type (type : expr) : string :=
list.as_string (list.map (λ c, if c = ',' then ':' else c) (prod.snd (type.to_string.to_list.split_at 3)))

meta def expr.to_string_aux : expr → list name → string
| (expr.app f arg) l := string.join ["(@", expr.to_string_aux f l, " ", expr.to_string_aux arg l, ")"]
| (expr.pi var_name bi var_type body) l :=
  string.join $ match bi with
  | binder_info.default := ["Pi (", var_name.to_string, " : ", expr.to_string_aux var_type l, "), ", expr.to_string_aux body (var_name::l)]
  | binder_info.implicit := ["Pi {", var_name.to_string, " : ", expr.to_string_aux var_type l, "}, ", expr.to_string_aux body (var_name::l)]
  | binder_info.strict_implicit := ["Pi ⦃", var_name.to_string, " : ", expr.to_string_aux var_type l, "⦄, ", expr.to_string_aux body (var_name::l)]
  | binder_info.inst_implicit := ["Pi [", var_name.to_string, " : ", expr.to_string_aux var_type l, "], ", expr.to_string_aux body (var_name::l)]
  | _ := []
  end
| (expr.var n) l := match list.nth l n with
                    | some name := name.to_string
                    | none := ""
                    end
| e l := expr.to_string e  -- assume there are no elets and lams

meta def expr.to_string' (e : expr) : string :=
string.replace "@(" "(" $ expr.to_string_aux e []

meta def emit_structure_here (s : structure_info) : lean.parser unit :=
do let fields := string.join $ list.map (λ (f : name × expr), string.join ["(", f.fst.to_string, " : ", (expr.to_string' f.snd), ") "])
                                        (list.zip s.field_names s.field_values),
   let str := string.replace ".{succ u}" ".{u + 1}" $
              string.replace ".{succ v}" ".{v + 1}" $
              string.join ["class ", s.structure_name.to_string, " ", pp_type s.type, " := ", fields],
   trace str,
   lean.parser.emit_code_here str

@[user_command]
meta def emit_homomorphism_structure_cmd (_ : interactive.parse $ lean.parser.tk "emit_homomorphism_structure") : lean.parser unit :=
do struct_name ← lean.parser.ident,
   s ← lean.parser.of_tactic $ homomorphism_structure struct_name,
   emit_structure_here s
   .

emit_homomorphism_structure ordered_ring
#print ordered_ring_homomorphism
