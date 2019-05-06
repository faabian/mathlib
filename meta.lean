/-
Copyright (c) 2019 Fabian Glöckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Glöckle

Generate categories of types with "has_x"-operators and compatible maps as morphisms.
-/

import algebra.group
import category_theory.concrete_category
open expr tactic

set_option trace.app_builder true
set_option pp.universes true
set_option pp.implicit true
set_option formatter.hide_full_terms false

-- example for a ternary operator
class has_ternary      (α : Type*) := (ternary : α → α → α → α)

-- do we need this dependently?
meta def arrow_list : expr → list expr
| (pi _ _ d b) := d :: (arrow_list b)
| (const t l)  := [const t l]
| (mvar n m e) := [mvar n m e]
| (var n)      := [var n]
| (sort n)     := [sort n]
| _            := []

meta def count_vars_aux : ℕ → list expr → ℕ
| n ((var m) :: tl) := ite (n + 1 = m) (count_vars_aux (n+1) tl) n
| n _               := n

meta def count_vars (l : list expr) : ℕ := count_vars_aux 0 (l.remove_nth (l.length - 1))

meta def codomain_type (l : list expr) : option expr := l.nth (l.length - 1)

meta def codomain_is_bound (l : list expr) : bool :=
match codomain_type l with
| some (var _) := tt
| _            := ff
end

meta def codomain_is_prop (l : list expr) : bool :=
match codomain_type l with
| some (sort level.zero) := tt
| _                      := ff
end

meta def arity_homog (x : string) : tactic ℕ :=
do let htt := name.mk_string x (name.mk_string (string.append "has_" x) name.anonymous),
  htc ← mk_const htt,
  t ← infer_type htc,
  let body := binding_body (binding_body t),
  return $ count_vars (arrow_list body)

meta def add_compatible_def (x : string): command :=
do let has_x_name := name.mk_string (string.append "has_" x) name.anonymous,
   let has_x_x_name := name.mk_string x has_x_name,
   let has_x : expr := expr.const has_x_name [level.zero],
   let has_x_x : expr := expr.const has_x_x_name [level.zero],
   t ← infer_type has_x_x,
   let body := binding_body (binding_body t),
   let arity := count_vars (arrow_list body),
   let target_self := codomain_is_bound (arrow_list body),
   let target_prop := codomain_is_prop (arrow_list body),
   α ← mk_local' `α binder_info.implicit (sort (level.succ level.zero)),
   β ← mk_local' `β binder_info.implicit (sort (level.succ level.zero)),
   i₁ ← mk_local' `i₁ binder_info.inst_implicit (has_x α),
   i₂ ← mk_local' `i₂ binder_info.inst_implicit (has_x β),
   type_main ← to_expr ``((%%α → %%β) → Prop),
   let decl_type := expr.pis [α, β, i₁, i₂] type_main,
   f ← mk_local' `f binder_info.default (pi `a binder_info.default α β),
   let nm := λ (n : ℕ), (name.mk_string (string.append "x" (to_string n)) name.anonymous),
   let vars := list.map
    (λ n, expr.local_const (nm n) (nm n) binder_info.implicit α)
    (list.range arity),
   let fs := list.map (λ x, some (f x)) vars,
   app₁ ← mk_mapp has_x_x_name ([some α, some i₁] ++ (list.map some vars)),
   app₂ ← mk_mapp has_x_x_name ([some β, some i₂] ++ fs),
   body_main ← if target_self then to_expr ``(%%f (%%app₁) = %%app₂)
               else (if target_prop then to_expr ``(%%app₁ ↔ %%app₂)
                     else to_expr ``(%%app₁ = %%app₂)),
   let decl_body := expr.lambdas [α, β, i₁, i₂, f] (expr.pis vars body_main),
   let decl_name := name.mk_string (string.append x "_compatible") name.anonymous,
   add_decl $ mk_definition decl_name [] decl_type decl_body  -- universes here
   -- todo: allow both → and ↔ for Prop-valued?

run_cmd add_compatible_def "mul"
run_cmd add_compatible_def "ternary"
run_cmd add_compatible_def "lt"
run_cmd add_compatible_def "to_string"
#print mul_compatible
#print ternary_compatible
#print lt_compatible
#print to_string_compatible

meta def add_compatible_id_lemma (x : string) : command :=
do let has_x_name := name.mk_string (string.append "has_" x) name.anonymous,
   let has_x_x_name := name.mk_string x has_x_name,
   let has_x : expr := expr.const has_x_name [level.zero],
   let has_x_x : expr := expr.const has_x_x_name [level.zero],
   let compatible := name.mk_string (string.append x "_compatible") name.anonymous,
   t ← infer_type has_x_x,
   let body := binding_body (binding_body t),
   let arity := count_vars (arrow_list body),
   α ← mk_local' `α binder_info.implicit (sort (level.succ level.zero)),
   i ← mk_local' `i binder_info.inst_implicit (has_x α),
   let ida : expr := const `id [level.succ level.zero],
   stmt ← mk_app compatible [α, α, i, i, ida α],
   let decl_type := expr.pis [α, i] stmt,
   let nm := λ (n : ℕ), (name.mk_string (string.append "x" (to_string n)) name.anonymous),
   let vars := list.map
    (λ n, expr.local_const (nm n) (nm n) binder_info.implicit α)
    (list.range arity),
   xs ← mk_app has_x_x_name ([i] ++ vars),
   rf ← mk_app `rfl [xs],
   let decl_body := expr.lambdas ([α, i] ++ vars) (rf),
   let decl_name := name.mk_string (string.append x "_compatible_id") name.anonymous,
   add_decl $ declaration.thm decl_name [] decl_type (task.pure decl_body)
   -- todo: Prop-valued

run_cmd add_compatible_id_lemma "ternary"
run_cmd add_compatible_id_lemma "to_string"
#print ternary_compatible_id
#print to_string_compatible_id

meta def add_compatible_comp_lemma (x : string) : command :=
do let has_x_name := name.mk_string (string.append "has_" x) name.anonymous,
   let has_x_x_name := name.mk_string x has_x_name,
   let has_x : expr := expr.const has_x_name [level.zero],
   let has_x_x : expr := expr.const has_x_x_name [level.zero],
   let compatible := name.mk_string (string.append x "_compatible") name.anonymous,
   t ← infer_type has_x_x,
   let body := binding_body (binding_body t),
   let arity := count_vars (arrow_list body),
   let target_prop := codomain_is_prop (arrow_list body),
   α ← mk_local' `α binder_info.implicit (sort (level.succ level.zero)),
   ia ← mk_local' `ia binder_info.inst_implicit (has_x α),
   β ← mk_local' `β binder_info.implicit (sort (level.succ level.zero)),
   ib ← mk_local' `ib binder_info.inst_implicit (has_x β),
   γ ← mk_local' `γ binder_info.implicit (sort (level.succ level.zero)),
   ic ← mk_local' `ic binder_info.inst_implicit (has_x γ),
   f ← mk_local' `f binder_info.implicit (pi `_x binder_info.default α β),
   g ← mk_local' `g binder_info.implicit (pi `_x binder_info.default β γ),
   comp_f ← mk_app compatible [α, β, ia, ib, f],
   comp_g ← mk_app compatible [β, γ, ib, ic, g],
   hf ← mk_local' `hf binder_info.default comp_f,
   hg ← mk_local' `hg binder_info.default comp_g,
   compos ← mk_mapp `function.comp [none, none, none, g, f],
   stmt ← mk_app compatible [α, γ, ia, ic, compos],
   let decl_type := expr.pis [α, β, γ, ia, ib, ic, f, g, hf, hg] stmt,
   let nm := λ (n : ℕ), (name.mk_string (string.append "x" (to_string n)) name.anonymous),
   let vars := list.map
    (λ n, expr.local_const (nm n) (nm n) binder_info.implicit α)
    (list.range arity),
   let fs := list.map (λ v, (f v)) vars,
   op ← mk_app has_x_x_name ([ia] ++ vars),
   let f_op := app f op,
   op_f ← mk_app has_x_x_name ([ib] ++ fs),
   let hf_vars := list.foldl (λ f x, app f x) hf vars,
   let hg_fs := list.foldl (λ f x, app f x) hg fs,
   proof ← (if target_prop then
              to_expr ``(iff.trans %%hf_vars %%hg_fs)
            else do congr ← mk_app `congr_arg [β, γ, f_op, op_f, g, hf_vars],
                    to_expr ``(eq.trans %%congr %%hg_fs)),
   let decl_body := expr.lambdas ([α, β, γ, ia, ib, ic, f, g, hf, hg] ++ vars) proof,
   let decl_name := name.mk_string (string.append x "_compatible_comp") name.anonymous,
   add_decl $ declaration.thm decl_name [] decl_type (task.pure decl_body)
-- e.g. λ x y, eq.trans (@congr_arg β γ (f (x * y)) (f x * f y) g (@hf x y)) (@hg (f x) (f y))
-- for any transitive target? eq, if, iff, ...

run_cmd add_compatible_comp_lemma "ternary"
#print ternary_compatible_comp

run_cmd add_compatible_comp_lemma "lt"
#print lt_compatible_comp

meta def add_concrete_category (x : string) : command :=
do let has_x_name := name.mk_string (string.append "has_" x) name.anonymous,
   let has_x : expr := expr.const has_x_name [level.zero],
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
   add_decl $ mk_definition decl_name [] decl_type decl_body

run_cmd add_concrete_category "ternary"
#print ternary_category

-- todo: fix universes

#print group  -- can we obtain the "extends monoid" information somehow, or is it inlined?
-- (this is esp. relevant for top_group extends top_space where we manually want to add the data for top_space)
