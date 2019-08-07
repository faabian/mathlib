/-
Copyright (c) 2019 Fabian Glöckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Glöckle

Generate categories corresponding to structures.
-/

import analysis.normed_space.basic  -- for example section
import algebra.group                -- for example section
import category_theory.concrete_category
open expr tactic

universes u v w

meta def codomain : expr → expr
| (pi _ _ _ b)  := codomain b
| e             := e

meta def field_name (field : expr) : string := (local_pp_name field).to_string

meta def compatibility_condition (struct_name : name) (base : expr) (α β i₁ i₂ f : expr)
  (field : expr) : tactic expr :=
do t ← infer_type field,
   let field_name_str := field_name field,
   let field_name := struct_name <.> field_name_str,
   arity ← get_pi_arity t,
   target_class ← is_class t,
   -- todo: use already defined homomorphisms for to_... fields of new style structures
   let target_self := (codomain t) =ₐ base,
   let target_prop := (codomain t) =ₐ sort level.zero,
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
   let target_prop := (codomain t) =ₐ sort level.zero,
   let field_name_str := field_name field,
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

meta def homomorphism_comp_part (struct_name : name) (base : expr) (α β γ ia ib ic f g hf hg : expr)
  (field : expr) (field_number : ℕ) (num_fields : ℕ): tactic expr :=
do t ← infer_type field,
   let target_prop := codomain t =ₐ sort level.zero,
   let field_name_str := field_name field,
   let field_name := struct_name <.> field_name_str,
   let hom_name := mk_simple_name (string.append struct_name.to_string "_homomorphism"),
   let hom_field_name := hom_name <.> field_name_str,
   arity ← get_pi_arity t,
   let nm := λ (n : ℕ), mk_simple_name (string.append "x" (to_string n)),
   let vars := list.map
    (λ n, expr.local_const (nm n) (nm n) binder_info.implicit α)
    (list.range arity),
   let fs := list.map (λ v, (f v)) vars,
   op ← mk_app field_name ([ia] ++ vars),
   let f_op := app f op,
   op_f ← mk_app field_name ([ib] ++ fs),
   hhf ← mk_mapp hom_field_name [some α, some β, some ia, some ib, some f, some hf] ,
   hhg ← mk_mapp hom_field_name [some β, some γ, some ib, some ic, some g, some hg],
   let hf_vars := expr.app_of_list hhf vars,
   let hg_fs := expr.app_of_list hhg fs,
   proof ← (if target_prop then
              to_expr ``(implies.trans %%hf_vars %%hg_fs)
            else do congr ← mk_app `congr_arg [β, γ, f_op, op_f, g, hf_vars],
                    to_expr ``(eq.trans %%congr %%hg_fs)),
   return (expr.lambdas vars proof)
-- for any transitive target? eq, if, iff, ...

meta def get_parameters (struct_name : name) : tactic (option (list expr)) :=
do env ← tactic.get_env,
   let constr := exceptional.to_option $ environment.get env struct_name,
   let t := option.map declaration.type constr,
   res ← traversable.traverse tactic.mk_local_pis t,
   return (option.map prod.fst res)

-- By a simple heuristic, a field is an argument to the constructor whose name is not the same as
-- a parameter's. E.g. for "group α", the α argument to the constructor is not considered a field.
meta def get_parameters_and_fields (struct_name : name) : tactic ((list expr) × (list expr)) :=
do env ← tactic.get_env,
   let mk_name := struct_name <.> "mk",
   let mk := exceptional.to_option $ environment.get env mk_name,
   let t := option.map declaration.type mk,
   res ← traversable.traverse tactic.mk_local_pis t,
   do fields ← (option.map prod.fst res),
      params_opt ← get_parameters struct_name,
      param_names ← option.map (list.map field_name) params_opt,
      return $ list.partition (λ f, field_name f ∈ param_names) fields

meta def is_data_field (field : expr) : tactic bool :=
do t ← infer_type field,
   (is_prop t) >>= (λ x, return (bnot x))  -- ??

meta def get_parameters_and_data_fields (struct_name : name) : tactic ((list expr) × (list expr)) :=
do (params, fields) ← get_parameters_and_fields struct_name,
   data_fields ← (list.mfilter is_data_field) fields,
   return (params, data_fields)

meta def id_homomorphism (struct_name : name) : tactic declaration :=
do (params, fields) ← get_parameters_and_data_fields struct_name,
   let base_type := params.head,
   let struct : expr :=  expr.const struct_name [level.param `v],
   let hom_name := mk_simple_name (string.append struct_name.to_string "_homomorphism"),
   let hom_constr_name := hom_name <.> "mk",
   α ← mk_local' `α binder_info.implicit (sort (level.succ (level.param `v))),
   i ← mk_local' `i binder_info.inst_implicit (struct α),
   let ida : expr := expr.const `id [level.succ (level.param `v)],
   compatibilities ← fields.mmap (homomorphism_id_part struct_name base_type α i ida),
   stmt ← mk_app hom_name [α, α, i, i, ida α],
   constr ← mk_mapp hom_constr_name [some α, some α, some i, some i, some (ida α)],
   let body := expr.app_of_list constr compatibilities,
   let decl_type := expr.pis [α, i] stmt,
   let decl_name := mk_simple_name (string.append struct_name.to_string "_id_homomorphism"),
   return (mk_definition decl_name (collect_univ_params decl_type) decl_type (expr.lambdas [α, i] body))

meta def add_id_homomorphism (struct_name : name) : command :=
do decl ← id_homomorphism struct_name,
   add_decl decl

meta def homomorphism_comp (struct_name : name) : tactic declaration :=
do (params, fields) ← get_parameters_and_data_fields struct_name,
   let base_type := params.head,
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
   let hom_name := mk_simple_name (string.append struct_name.to_string "_homomorphism"),
   let hom_constr_name := hom_name <.> "mk",
   hom_f ← mk_app hom_name [α, β, ia, ib, f],
   hom_g ← mk_app hom_name [β, γ, ib, ic, g],
   hf ← mk_local' `hf binder_info.default hom_f,
   hg ← mk_local' `hg binder_info.default hom_g,
   compos ← mk_mapp `function.comp [none, none, none, g, f],
   stmt ← mk_app hom_name [α, γ, ia, ic, compos],
   let field_numbers := list.range fields.length,
   let fields_enum := list.zip fields field_numbers,
   compatibilities ← fields_enum.mmap
    (λ field_enum, homomorphism_comp_part struct_name base_type α β γ ia ib ic f g hf hg
                    field_enum.fst field_enum.snd fields_enum.length),
   constr ← mk_mapp hom_constr_name [some α, some γ, some ia, some ic, some compos],
   let body := expr.app_of_list constr compatibilities,
   let decl_body := expr.lambdas [α, β, γ, ia, ib, ic, f, g, hf, hg] body,
   let decl_type := expr.pis [α, β, γ, ia, ib, ic, f, g, hf, hg] stmt,
   let decl_name := mk_simple_name (string.append struct_name.to_string "_homomorphism_comp"),
   return $ declaration.thm decl_name (collect_univ_params decl_type) decl_type (task.pure decl_body)
-- for any transitive target? eq, if, iff, ...

meta def add_homomorphism_comp (struct_name : name) : command :=
do decl ← homomorphism_comp struct_name,
   add_decl decl

meta structure structure_info :=
(structure_name   : name)
(type             : expr)
(field_names      : list name)
(field_values     : list expr)
(flat             : bool := ff)
(extend           : list string := [])

def find_all {α : Type*} [decidable_eq α] (l : list α) (pattern : list α) : list ℕ :=
list.filter (λ n, list.is_prefix_of pattern (prod.snd (list.split_at n l))) (list.range l.length)

def split_aux {α : Type*} [decidable_eq α] : list ℕ → list α → ℕ → ℕ → list (list α)
| [] l offset jump      := [l]
| (hi::ti) l offset jump := (list.split_at (hi - offset) l).1 :: (split_aux ti (list.split_at jump (list.split_at (hi - offset) l).2).2 (hi + jump) jump)

def split {α : Type*} [decidable_eq α] (l : list α) (pattern : list α) : list (list α) :=
split_aux (find_all l pattern) l 0 (pattern.length)

def list.replace {α : Type*} [decidable_eq α] (l : list α) (pattern : list α) (replace_with : list α) : list α :=
list.intercalate replace_with (split l pattern)

def string.replace (pattern : string) (replace_with : string) (s : string) : string :=
list.as_string (list.replace s.to_list pattern.to_list replace_with.to_list)

meta def homomorphism_structure (struct_name : name) : tactic structure_info :=
do (params, fields) ← get_parameters_and_data_fields struct_name,
   let base_type := params.head,
   let field_names := fields.map local_pp_name,
   let struct_u : expr :=  expr.const struct_name [level.param `u],
   let struct_v : expr :=  expr.const struct_name [level.param `v],
   α ← mk_local' `α binder_info.implicit (sort (level.succ (level.param `u))),
   β ← mk_local' `β binder_info.implicit (sort (level.succ (level.param `v))),
   i₁ ← mk_local' `i₁ binder_info.inst_implicit (struct_u α),
   i₂ ← mk_local' `i₂ binder_info.inst_implicit (struct_v β),
   f ← mk_local' `f binder_info.default (pi `ff binder_info.default α β),
   compatibilities ← fields.mmap (compatibility_condition struct_name base_type α β i₁ i₂ f),
   type_main ← to_expr ``(Prop),
   let struct_type := expr.pis [α, β, i₁, i₂, f] type_main,
   let struct_name := mk_simple_name (string.append struct_name.to_string "_homomorphism"),
   return ⟨struct_name, struct_type, field_names, compatibilities, ff, []⟩

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
   lean.parser.emit_code_here str

@[user_command]
meta def emit_homomorphism_structure_cmd (_ : interactive.parse $ lean.parser.tk "emit_homomorphism_structure") : lean.parser unit :=
do struct_name ← lean.parser.ident,
   s ← lean.parser.of_tactic $ homomorphism_structure struct_name,
   emit_structure_here s
   .

def to_upper (c : char) : char :=
let n := char.to_nat c in
if n >= 65 + 32 ∧ n <= 90 + 32 then char.of_nat (n - 32) else c

def capitalize : string → string
| "" := ""
| ⟨hd :: tl⟩ := ⟨(to_upper hd) :: tl⟩

def camel_case (s : string) : string :=
string.join $ list.map capitalize (s.split (λ c, c = '_'))

meta def bundled_declaration (struct_name : name) : tactic declaration :=
do let decl_name := camel_case struct_name.to_string,
   let decl_type : expr := sort (level.succ (level.succ (level.param `u))),
   let grp : expr := expr.const struct_name [level.param `u],
   decl_body ← to_expr ``(category_theory.bundled %%grp),
   return (mk_definition decl_name (collect_univ_params decl_type) decl_type decl_body)

meta def add_bundled_declaration (struct_name : name) : command :=
do decl ← bundled_declaration struct_name,
   add_decl decl

meta def concrete_category_declaration (struct_name : name) : tactic declaration :=
do let struct : expr := const struct_name [level.param `u],
   let struct_name_s := struct_name.to_string,
   let id_lemma_name := name.mk_string (string.append struct_name_s "_id_homomorphism") name.anonymous,
   let comp_lemma_name := name.mk_string (string.append struct_name_s "_homomorphism_comp") name.anonymous,
   let id_lemma : expr := expr.const id_lemma_name [level.param `u],
   let comp_lemma : expr := expr.const comp_lemma_name [level.param `u, level.param `u, level.param `u],
   let hom_name := mk_simple_name (string.append struct_name_s "_homomorphism"),
   let hom : expr := const hom_name [level.param `u, level.param `u],
   let cc_name := (name.mk_string "category_theory" name.anonymous) <.> "concrete_category",
   let cc_constr_name := cc_name <.> "mk",
   decl_type ← mk_app cc_name [struct, hom],
   decl_body ← mk_app cc_constr_name [struct, hom, id_lemma, comp_lemma],
   let decl_name := name.mk_string (string.append struct_name.to_string "_category") name.anonymous,
   return $ mk_definition decl_name (collect_univ_params decl_type) decl_type decl_body

meta def add_concrete_category (struct_name : name) : command :=
do decl ← concrete_category_declaration struct_name,
   add_decl decl

meta def add_instance_attribute (s : string) : lean.parser unit :=
do let str := string.append "attribute [instance] " s,
   lean.parser.emit_code_here str

meta def add_instance_attribute_category (struct_name : name) : lean.parser unit :=
add_instance_attribute (struct_name.to_string ++ "_category")

@[user_command]
meta def add_instance_attribute_cmd (_ : interactive.parse $ lean.parser.tk "user_add_instance_attribute") : lean.parser unit :=
do ident ← lean.parser.ident,
   add_instance_attribute ident.to_string

@[user_command]
meta def add_category_instance_cmd (_ : interactive.parse $ lean.parser.tk "user_add_category_instance") : lean.parser unit :=
do struct_name ← lean.parser.ident,
   add_instance_attribute_category struct_name

-- extract fields by the simple heuristic of looking for the same field names
meta def extract_fields (needed : list string) (given_fields : list expr) (given : list string) : list expr :=
let given := list.zip given_fields given in
let filter_function := λ needed (field : expr × string), field.2 = needed in
list.join (list.map (λ n, list.map prod.fst (list.filter (filter_function n) given)) needed)

-- helper function for debugging terms (which should not contain local constants)
meta def find_local_constant : expr → list expr
| (local_const nm pnm bi ty) := [local_const nm pnm bi ty]
| (app f x) := (find_local_constant f) ++ (find_local_constant x)
| (lam nm bi type body) := (find_local_constant type) ++ (find_local_constant body)
| (pi nm bi type body) := (find_local_constant type) ++ (find_local_constant body)
| _ := []

-- count difference between "up" and "down" symbols in a term
def list.level_aux  {α : Type u} [decidable_eq α] (up : α) (down : α) : ℕ → list α → ℕ
| n [] := n
| n (c :: tail) := if (c = up) then list.level_aux (n + 1) tail
                   else if (c = down) then list.level_aux (n - 1) tail
                   else list.level_aux n tail

def list.level {α : Type u} [decidable_eq α] (up : α) (down : α) (l : list α) : ℕ :=
list.level_aux up down 0 l

-- expects nested bracket terms to be well-formed and removes all brackets
def list.remove_brackets {α : Type u} [decidable_eq α] (opener : α) (closer : α) (l : list α) : list α :=
list.map prod.snd (list.filter (λ p, list.level opener closer (l.take p.fst) = 0 ∧ p.snd ≠ opener) l.enum)

def string.remove_brackets (opener : char) (closer : char) (s : string) : string :=
list.as_string $ list.remove_brackets opener closer s.to_list

def list.remove_last_if_eq {α : Type u} [decidable_eq α] [inhabited α] (a : α) (l : list α) : list α :=
if l.reverse.head = a then l.take (l.length - 1) else l

def string.remove_last_if_eq (c : char) (s : string) : string :=
list.as_string $ list.remove_last_if_eq c s.to_list

-- removes (neighboring) duplicates of given symbol
-- (l should not be empty)
def list.remove_duplicates_of {α : Type u} [decidable_eq α] [inhabited α] (a : α) (l : list α) : list α :=
l.head :: list.map prod.snd (list.filter (λ p, not $ p.fst = p.snd ∧ p.fst = a) (list.zip l l.tail))

def string.remove_duplicates_of (c : char) (s : string) : string :=
list.as_string $ list.remove_duplicates_of c s.to_list

def remove_universe_annotation (s : string) : string :=
string.remove_last_if_eq '.' $ string.remove_duplicates_of '.' $ string.remove_brackets '{' '}' s

meta def infer_param_instances (needed_params : list expr) (given_params : list expr) : tactic (list expr) :=
list.mmap (
  λ (p : expr × expr), do
    t₁ ← infer_type p.fst,
    t₂ ← infer_type p.snd,
    -- if t₁ = t₂ then (return p.snd) else (mk_instance t₁)  -- how can we use typeclass resolution?
    cls ← is_class t₁,
    if (cls ∧ t₁ ≠ t₂) then ( do
      let converter_name : name :=
        name.mk_string (string.join
          [remove_universe_annotation (get_app_fn t₂).to_string, "_to_", remove_universe_annotation (get_app_fn t₁).to_string])
          name.anonymous,
      mk_app converter_name [p.snd])
    else (return p.snd)
) (list.zip needed_params given_params)

meta def sort_level : expr → option level
| (sort l) := some l
| _ := none

meta def get_universes (l : list expr) : tactic (list level) :=
do types ← list.mmap infer_type l,
   return $ list.join $ list.map (option.to_list ∘ sort_level) types

meta def level.pred : level → level
| (level.succ l) := l
| l              := l

-- imitate {..} unpacking
meta def projection_declaration (struct_name₁ : name) (struct_name₂ : name) : tactic declaration :=
do (params₁, fields₁) ← get_parameters_and_fields struct_name₁,
   (params₂, fields₂) ← get_parameters_and_fields struct_name₂,
   levels ← get_universes params₁,
   let univs := list.map level.pred levels,
   let names₁ := list.map field_name fields₁,
   let names₂ := list.map field_name fields₂,
   let extracted_fields := extract_fields names₂ fields₁ names₁,
   let struct₁ : expr := const struct_name₁ univs,
   let struct₂ : expr := const struct_name₂ univs,
   let struct₂_constr_name := struct_name₂ <.> "mk",
   i ← mk_local' `i binder_info.inst_implicit (mk_app struct₁ params₁),
   let constr : expr := const struct₂_constr_name univs,
   params ← infer_param_instances params₂ params₁,
   let stmt : expr := mk_app struct₂ params,
   let fields : list expr := list.map
     (λ f, (mk_app (const (struct_name₁ <.> (field_name f)) univs) params₁ i))
     extracted_fields,
   let body := expr.app_of_list (mk_app constr params) fields,
   let decl_type := expr.pis (params₁ ++ [i]) stmt,
   let decl_name := mk_simple_name (string.join [struct_name₁.to_string, "_to_", struct_name₂.to_string]),
   return (mk_definition decl_name (collect_univ_params decl_type) decl_type (expr.lambdas (params₁ ++ [i]) body))
   -- todo: warning, if not (types₂ ⊆ types₁) then fail "First structure type is not an extension of second structure type."

meta def add_projection  (struct_name₁ : name) (struct_name₂ : name) : command :=
do decl ← (projection_declaration struct_name₁ struct_name₂),
   add_decl decl

meta def forgetful_functor_declaration (struct_name₁ struct_name₂ : name) : tactic declaration :=
do let struct₁ : expr  := const struct_name₁ [level.param `u],
   let struct₂ : expr  := const struct_name₂ [level.param `u],
   decl_type ← to_expr ``(category_theory.functor (category_theory.bundled %%struct₁) (category_theory.bundled %%struct₂)),
   let hom₁ : expr := const (name.mk_string (struct_name₁.to_string ++ "_homomorphism") name.anonymous) [level.param `u, level.param `u],
   let hom₂ : expr := const (name.mk_string (struct_name₂.to_string ++ "_homomorphism") name.anonymous) [level.param `u, level.param `u],
   let cat₁ : expr := const (name.mk_string (struct_name₁.to_string ++ "_category") name.anonymous) [level.param `u],
   let cat₂ : expr := const (name.mk_string (struct_name₂.to_string ++ "_category") name.anonymous) [level.param `u],
   let obj : expr := const (name.mk_string (string.join [struct_name₁.to_string, "_to_", struct_name₂.to_string]) name.anonymous) [level.param `u],
   let hom : expr := const (name.mk_string (string.join [struct_name₁.to_string, "_homomorphism_to_", struct_name₂.to_string, "_homomorphism"]) name.anonymous) [level.param `u, level.param `u],
   decl_body ← to_expr ``(@category_theory.concrete_functor %%struct₁ %%hom₁ %%cat₁ %%struct₂ %%hom₂ %%cat₂ %%obj %%hom),
   let decl_name := name.mk_string (string.join ["forgetful_", struct_name₁.to_string, "_to_", struct_name₂.to_string]) name.anonymous,
   return $ mk_definition decl_name (collect_univ_params decl_type) decl_type decl_body

meta def add_forgetful_functor (struct_name₁ struct_name₂ : name) : command :=
do decl ← forgetful_functor_declaration struct_name₁ struct_name₂,
   add_decl decl

meta def register_structure (struct_name : name) : lean.parser unit :=
do s ← lean.parser.of_tactic $ homomorphism_structure struct_name,
   emit_structure_here s,
   add_bundled_declaration struct_name,
   add_id_homomorphism struct_name,
   add_homomorphism_comp struct_name,
   add_concrete_category struct_name,
   add_instance_attribute_category struct_name.to_string

meta def register_forgetful (struct_name₁ struct_name₂ : name) : lean.parser unit :=
do add_projection struct_name₁ struct_name₂,
   let hom₁ := name.mk_string (struct_name₁.to_string ++ "_homomorphism") name.anonymous,
   let hom₂ := name.mk_string (struct_name₂.to_string ++ "_homomorphism") name.anonymous,
   add_projection hom₁ hom₂,
   let forgetful_obj := name.mk_string (string.join [struct_name₁.to_string, "_to_", struct_name₂.to_string]) name.anonymous,
   let forgetful_hom := name.mk_string (string.join [struct_name₁.to_string, "_homomorphism_to_", struct_name₂.to_string, "_homomorphism"]) name.anonymous,
   add_instance_attribute forgetful_obj.to_string,
   add_instance_attribute forgetful_hom.to_string,
   add_forgetful_functor struct_name₁ struct_name₂

@[user_command]
meta def register_structure_cmd (_ : interactive.parse $ lean.parser.tk "register_structure") : lean.parser unit :=
do struct_name ← lean.parser.ident,
   register_structure struct_name
   .

@[user_command]
meta def register_forgetful_cmd (_ : interactive.parse $ lean.parser.tk "register_forgetful_functor") : lean.parser unit :=
do struct_name₁ ← lean.parser.ident,
   struct_name₂ ← lean.parser.ident,
   register_forgetful struct_name₁ struct_name₂
   .

-- Examples

-- Generate homomorphism structure and concrete category for group structure. The lemmas on
-- compositions and identities are auto-generated.
-- (The code only uses the definition of the group structure.)

register_structure group

-- This does the following:

-- emit_homomorphism_structure group
-- #print group_homomorphism
-- #check @group_homomorphism.mul
-- run_cmd add_bundled_declaration `group
-- #check Group
-- run_cmd add_id_homomorphism `group
-- run_cmd add_homomorphism_comp `group
-- #check group_homomorphism_comp
-- run_cmd add_concrete_category `group
-- user_add_category_instance group
-- #check group_category
-- #check (by apply_instance : category_theory.category (category_theory.bundled group))

-- Similarly, define the category of monoids.

register_structure monoid

-- Define the forgetful functor from groups to monoids. The code assumes that group contains at least
-- all fields that monoid has.

register_forgetful_functor group monoid

-- The code does the following:

-- run_cmd add_projection `group `monoid
-- run_cmd add_projection `group_homomorphism `monoid_homomorphism
-- #check group_to_monoid
-- #check group_homomorphism_to_monoid_homomorphism
-- attribute [instance] group_to_monoid
-- attribute [instance] group_homomorphism_to_monoid_homomorphism
-- variables (α : Type u) (β : Type v) [group α] [group β] (f : α → β) [group_homomorphism f]
-- #check (by apply_instance : monoid α)
-- #check (by apply_instance : monoid_homomorphism f)

register_structure ordered_comm_group
register_structure add_group

-- This works for all algebraic structures. For other structures, "weak homomorphisms" are generated
-- for propositional fields (e. g. x ≤ y → f x ≤ f y). However, assuming all fields of the structure
-- to be relevant for homomorphisms can lead to wrong behavior. For instance, if a structure extends
-- both has_le and has_lt, then weak homomorphisms will have to satisfy both
-- x ≤ y → f x ≤ f y   and   x < y → f x < f y,
-- an atypical choice.

#print ordered_comm_group_homomorphism

-- For "new style" structures (with "to_..."-projections to structures they extend), the code does
-- not (yet) work, but it can easily be adapted.

-- #print normed_group
-- register_structure normed_group  -- currently does not work

-- A good approach would be a "library" of structures and their corresponding homomorphism types in
-- case they cannot be auto-generated (for topological spaces, or preorders, see above). These could
-- then be used to generate homomorphism types for structures derived from these.
