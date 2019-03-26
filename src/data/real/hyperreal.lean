/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/

import data.real.basic algebra.field order.filter.filter_product analysis.specific_limits
local attribute [instance] classical.prop_decidable

open filter filter.filter_product

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
@[reducible] def hyperreal := filter.filterprod ℝ (@hyperfilter ℕ)

namespace hyperreal

notation `ℝ*` := hyperreal

private def U := is_ultrafilter_hyperfilter set.infinite_univ_nat
noncomputable instance : discrete_linear_ordered_field ℝ* := filter_product.discrete_linear_ordered_field U

/-- A sample infinitesimal hyperreal-/
noncomputable def epsilon : ℝ* := of_seq (λ n, n⁻¹)

/-- A sample infinite hyperreal-/
noncomputable def omega : ℝ* := of_seq (λ n, n)

local notation `ε` := epsilon
local notation `ω` := omega

lemma epsilon_eq_inv_omega : ε = ω⁻¹ := rfl

lemma inv_epsilon_eq_omega : ε⁻¹ = ω := @inv_inv' _ _ ω

lemma epsilon_pos : 0 < ε :=
have h0' : {n : ℕ | ¬ n > 0} = {0} := 
by simp only [not_lt, (set.set_of_eq_eq_singleton).symm]; ext; exact nat.le_zero_iff,
begin
  rw lt_def U,
  show {i : ℕ | (0 : ℝ) < i⁻¹} ∈ hyperfilter.sets,
  simp only [inv_pos', nat.cast_pos],
  exact mem_hyperfilter_of_finite_compl set.infinite_univ_nat (by convert set.finite_singleton _),
end

lemma epsilon_ne_zero : ε ≠ 0 := ne_of_gt epsilon_pos

lemma omega_pos : 0 < ω := by rw ←inv_epsilon_eq_omega; exact inv_pos epsilon_pos

lemma omega_ne_zero : ω ≠ 0 := ne_of_gt omega_pos

theorem epsilon_mul_omega : ε * ω = 1 := @inv_mul_cancel _ _ ω omega_ne_zero

lemma lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : tendsto f at_top (nhds 0)) :
  ∀ {r : ℝ}, r > 0 → of_seq f < (r : ℝ*) :=
begin
  simp only [metric.tendsto_at_top, dist_zero_right, norm, lt_def U] at hf ⊢,
  intros r hr, cases hf r hr with N hf',
  have hs : -{i : ℕ | f i < r} ⊆ {i : ℕ | i ≤ N} :=
    λ i hi1, le_of_lt (by simp only [lt_iff_not_ge];
    exact λ hi2, hi1 (lt_of_le_of_lt (le_abs_self _) (hf' i hi2)) : i < N),
  exact mem_hyperfilter_of_finite_compl set.infinite_univ_nat 
    (set.finite_subset (set.finite_le_nat N) hs)
end

lemma neg_lt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : tendsto f at_top (nhds 0)) :
  ∀ {r : ℝ}, r > 0 → (-r : ℝ*) < of_seq f :=
λ r hr, have hg : _ := tendsto_neg hf,
neg_lt_of_neg_lt (by rw [neg_zero] at hg; exact lt_of_tendsto_zero_of_pos hg hr)

lemma gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : tendsto f at_top (nhds 0)) :
  ∀ {r : ℝ}, r < 0 → (r : ℝ*) < of_seq f :=
λ r hr, have hn : (r : ℝ*) = -↑(-r) := by rw [←of_eq_coe, ←of_eq_coe, of_neg, neg_neg],
by rw hn; exact neg_lt_of_tendsto_zero_of_neg hf (neg_pos.mpr hr)

lemma epsilon_lt_pos (x : ℝ) : x > 0 → ε < of x := lt_of_tendsto_zero_of_pos tendsto_inverse_at_top_nhds_0_nat

/-- Standard part predicate -/
def is_st (x : ℝ*) (r : ℝ) := ∀ δ : ℝ, δ > 0 → (r - δ : ℝ*) < x ∧ x < r + δ

/-- Standard part function: like a "round" to ℝ instead of ℤ -/
noncomputable def st : ℝ* → ℝ := 
λ x, if h : ∃ r, is_st x r then classical.some h else 0

/-- A hyperreal number is infinitesimal if its standard part is 0 -/
def infinitesimal (x : ℝ*) := is_st x 0

/-- A hyperreal number is positive infinite if it is larger than all real numbers -/
def infinite_pos (x : ℝ*) := ∀ r : ℝ, x > r

/-- A hyperreal number is negative infinite if it is smaller than all real numbers -/
def infinite_neg (x : ℝ*) := ∀ r : ℝ, x < r

/-- A hyperreal number is infinite if it is larger than all real numbers or smaller than all real numbers -/
def infinite (x : ℝ*) := infinite_pos x ∨ infinite_neg x

-- SOME FACTS ABOUT ST

private lemma is_st_unique_1 (x : ℝ*) (r s : ℝ) (hr : is_st x r) (hs : is_st x s) (hrs : r < s) : false :=
have hrs' : _ := half_pos $ sub_pos_of_lt hrs,
have hr' : _ := (hr _ hrs').2,
have hs' : _ := (hs _ hrs').1,
have h : s + -((s - r) / 2) = r + (s - r) / 2 := by linarith,
by simp only [(of_eq_coe _).symm, sub_eq_add_neg (of s), (of_neg _).symm, (of_add _ _).symm, h] at hr' hs';
  exact not_lt_of_lt hs' hr'

theorem is_st_unique {x : ℝ*} {r s : ℝ} (hr : is_st x r) (hs : is_st x s) : r = s :=
begin
  rcases lt_trichotomy r s with h | h | h,
  { exact false.elim (is_st_unique_1 x r s hr hs h) },
  { exact h },
  { exact false.elim (is_st_unique_1 x s r hs hr h) }
end

theorem not_infinite_of_exist_st {x : ℝ*} : (∃ r : ℝ, is_st x r) → ¬ infinite x := 
λ he hi, Exists.dcases_on he $ λ r hr, hi.elim 
   (λ hip, not_lt_of_lt (hr 2 two_pos).2 (hip $ r + 2))
   (λ hin, not_lt_of_lt (hr 2 two_pos).1 (hin $ r - 2))

theorem exist_st_of_not_infinite {x : ℝ*} (hni : ¬ infinite x) : ∃ r : ℝ, is_st x r := 
have hnile : _ := not_forall.mp (not_or_distrib.mp hni).1, 
have hnige : _ := not_forall.mp (not_or_distrib.mp hni).2,
let S : set ℝ := {y : ℝ | ↑y < x} in
let R : _ := real.Sup S in
Exists.dcases_on hnile (Exists.dcases_on hnige (λ r₁ hr₁ r₂ hr₂,
have HR₁ : ∃ y : ℝ, y ∈ S := ⟨r₁ - 1, lt_of_lt_of_le (of_lt_of_lt U (sub_one_lt _)) (not_lt.mp hr₁)⟩,
have HR₂ : ∃ z : ℝ, ∀ y ∈ S, y ≤ z := ⟨r₂, λ y hy, le_of_lt ((of_lt U).mpr (lt_of_lt_of_le hy (not_lt.mp hr₂)))⟩,
⟨R, λ δ hδ, 
  ⟨lt_of_not_ge' (λ c,
    have hc : ∀ y ∈ S, y ≤ R - δ := λ y hy, (of_le U.1).mpr (le_of_lt (lt_of_lt_of_le hy c)),
    not_lt_of_le ((real.Sup_le _ HR₁ HR₂).mpr hc) (sub_lt_self R hδ)), 
   lt_of_not_ge' (λ c,
    have hc : ↑(R + δ / 2) < x := lt_of_lt_of_le (add_lt_add_left (of_lt_of_lt U (half_lt_self hδ)) ↑R) c,
    not_lt_of_le (real.le_Sup _ HR₂ hc) ((lt_add_iff_pos_right _).mpr (half_pos hδ)))⟩⟩))

theorem exist_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, is_st x r) ↔ ¬ infinite x := 
⟨ not_infinite_of_exist_st, exist_st_of_not_infinite ⟩

theorem infinite_iff_not_exist_st {x : ℝ*} : infinite x ↔ ¬ ∃ r : ℝ, is_st x r := iff_not_comm.mp exist_st_iff_not_infinite

theorem st_infinite {x : ℝ*} (hi : infinite x) : st x = 0 := 
begin
  unfold st, split_ifs,
  { exact false.elim ((infinite_iff_not_exist_st.mp hi) h) },
  { refl }
end

lemma st_of_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r): st x = r :=
begin
  unfold st, split_ifs,
  { exact is_st_unique (classical.some_spec h) hxr },
  { exact false.elim (h ⟨r, hxr⟩) }
end

lemma is_st_st_of_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : is_st x (st x) := by rwa [st_of_is_st hxr]

lemma is_st_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, is_st x r) : is_st x (st x) :=
Exists.dcases_on hx (λ r, is_st_st_of_is_st)

lemma is_st_st {x : ℝ*} (hx : st x ≠ 0) : is_st x (st x) := 
begin
  unfold st, split_ifs,
  { exact classical.some_spec h },
  { exact false.elim (hx (by unfold st; split_ifs; refl)) }
end

lemma is_st_st' {x : ℝ*} (hx : ¬ infinite x) : is_st x (st x) := is_st_st_of_exists_st $ exist_st_of_not_infinite hx

lemma is_st_refl_real (r : ℝ) : is_st r r := 
λ δ hδ, ⟨sub_lt_self _ (of_lt_of_lt U hδ), (lt_add_of_pos_right _ (of_lt_of_lt U hδ))⟩

lemma st_id_real (r : ℝ) : st r = r := st_of_is_st (is_st_refl_real  r)

lemma eq_of_is_st_real {r s : ℝ} : is_st r s → r = s := is_st_unique (is_st_refl_real r)

lemma is_st_real_iff_eq {r s : ℝ} : is_st r s ↔ r = s := ⟨eq_of_is_st_real, λ hrs, by rw [hrs]; exact is_st_refl_real s⟩

lemma is_st_symm_real {r s : ℝ} : is_st r s ↔ is_st s r := by rw [is_st_real_iff_eq, is_st_real_iff_eq, eq_comm]

lemma is_st_trans_real {r s t : ℝ} : is_st r s → is_st s t → is_st r t := by rw [is_st_real_iff_eq, is_st_real_iff_eq, is_st_real_iff_eq]; exact eq.trans

lemma is_st_inj_real {r₁ r₂ s : ℝ} (h1 : is_st r₁ s) (h2 : is_st r₂ s) : r₁ = r₂ := 
eq.trans (eq_of_is_st_real h1) (eq_of_is_st_real h2).symm

-- BASIC LEMMAS ABOUT INFINITE

lemma infinite_pos_def {x : ℝ*} : infinite_pos x ↔ ∀ r : ℝ, x > r := by rw iff_eq_eq; refl

lemma infinite_neg_def {x : ℝ*} : infinite_neg x ↔ ∀ r : ℝ, x < r := by rw iff_eq_eq; refl

lemma ne_zero_of_infinite {x : ℝ*} : infinite x → x ≠ 0 := 
λ hI h0, or.cases_on hI 
  (λ hip, lt_irrefl (0 : ℝ*) ((by rwa ←h0 : infinite_pos 0) 0))
  (λ hin, lt_irrefl (0 : ℝ*) ((by rwa ←h0 : infinite_neg 0) 0))

lemma not_infinite_zero : ¬ infinite 0 := λ hI, ne_zero_of_infinite hI rfl

lemma pos_of_infinite_pos {x : ℝ*} : infinite_pos x → x > 0 := λ hip, hip 0

lemma neg_of_infinite_neg {x : ℝ*} : infinite_neg x → x < 0 := λ hin, hin 0

lemma not_infinite_pos_of_infinite_neg {x : ℝ*} : infinite_neg x → ¬ infinite_pos x := 
λ hn hp, not_lt_of_lt (hn 1) (hp 1)

lemma not_infinite_neg_of_infinite_pos {x : ℝ*} : infinite_pos x → ¬ infinite_neg x := 
imp_not_comm.mp not_infinite_pos_of_infinite_neg

lemma infinite_neg_neg_of_infinite_pos {x : ℝ*} : infinite_pos x → infinite_neg (-x) := λ hp r, neg_lt.mp (hp (-r))

lemma infinite_pos_neg_of_infinite_neg {x : ℝ*} : infinite_neg x → infinite_pos (-x) := λ hp r, lt_neg.mp (hp (-r))

lemma infinite_neg_neg_iff_infinite_pos {x : ℝ*} : infinite_pos x ↔ infinite_neg (-x) := 
⟨infinite_neg_neg_of_infinite_pos, λ hin, neg_neg x ▸ infinite_pos_neg_of_infinite_neg hin⟩

lemma infinite_pos_neg_iff_infinite_neg {x : ℝ*} : infinite_neg x ↔ infinite_pos (-x) := 
⟨infinite_pos_neg_of_infinite_neg, λ hin, neg_neg x ▸ infinite_neg_neg_of_infinite_pos hin⟩

lemma not_infinite_of_infinitesimal {x : ℝ*} : infinitesimal x → ¬ infinite x := 
λ hi hI, have hi' : _ := (hi 2 two_pos), or.dcases_on hI 
  (λ hip, have hip' : _ := hip 2, not_lt_of_lt hip' (by convert hi'.2; exact (zero_add 2).symm)) 
  (λ hin, have hin' : _ := hin (-2), not_lt_of_lt hin' (by convert hi'.1; exact (zero_sub 2).symm))

lemma not_infinitesimal_of_infinite {x : ℝ*} : infinite x → ¬ infinitesimal x := imp_not_comm.mp not_infinite_of_infinitesimal

lemma not_infinitesimal_of_infinite_pos {x : ℝ*} : infinite_pos x → ¬ infinitesimal x := 
λ hp, not_infinitesimal_of_infinite (or.inl hp)

lemma not_infinitesimal_of_infinite_neg {x : ℝ*} : infinite_neg x → ¬ infinitesimal x := 
λ hn, not_infinitesimal_of_infinite (or.inr hn)

lemma infinite_pos_iff_infinite_and_pos {x : ℝ*} : infinite_pos x ↔ (infinite x ∧ x > 0) := 
⟨λ hip, ⟨or.inl hip, hip 0⟩, λ ⟨hi, hp⟩, hi.cases_on (λ hip, hip) (λ hin, false.elim (not_lt_of_lt hp (hin 0)))⟩ 

lemma infinite_neg_iff_infinite_and_neg {x : ℝ*} : infinite_neg x ↔ (infinite x ∧ x < 0) := 
⟨λ hip, ⟨or.inr hip, hip 0⟩, λ ⟨hi, hp⟩, hi.cases_on (λ hin, false.elim (not_lt_of_lt hp (hin 0))) (λ hip, hip)⟩ 

lemma infinite_pos_iff_infinite_of_pos {x : ℝ*} (hp : x > 0) : infinite_pos x ↔ infinite x := 
by rw [infinite_pos_iff_infinite_and_pos]; exact ⟨λ hI, hI.1, λ hI, ⟨hI, hp⟩⟩

lemma infinite_pos_iff_infinite_of_nonneg {x : ℝ*} (hp : x ≥ 0) : infinite_pos x ↔ infinite x := 
or.cases_on (lt_or_eq_of_le hp) (infinite_pos_iff_infinite_of_pos)
  (λ h, by rw h.symm; exact ⟨λ hIP, false.elim (not_infinite_zero (or.inl hIP)), λ hI, false.elim (not_infinite_zero hI)⟩)

lemma infinite_neg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : infinite_neg x ↔ infinite x := 
by rw [infinite_neg_iff_infinite_and_neg]; exact ⟨λ hI, hI.1, λ hI, ⟨hI, hn⟩⟩

lemma infinite_pos_abs_iff_infinite_abs {x : ℝ*} : infinite_pos (abs x) ↔ infinite (abs x) := 
infinite_pos_iff_infinite_of_nonneg (abs_nonneg _)

lemma infinite_iff_infinite_pos_abs {x : ℝ*} : infinite x ↔ infinite_pos (abs x) := 
⟨ λ hi d, or.cases_on hi 
   (λ hip, by rw [abs_of_pos (hip 0)]; exact hip d) 
   (λ hin, by rw [abs_of_neg (hin 0)]; exact lt_neg.mp (hin (-d))), 
  λ hipa, by { rcases (lt_trichotomy x 0) with h | h | h,
    { exact or.inr (infinite_pos_neg_iff_infinite_neg.mpr (by rwa abs_of_neg h at hipa)) },
    { exact false.elim (ne_zero_of_infinite (or.inl (by rw [h]; rwa [h, abs_zero] at hipa)) h) },
    { exact or.inl (by rwa abs_of_pos h at hipa) } } ⟩ 

lemma infinite_iff_infinite_abs {x : ℝ*} : infinite x ↔ infinite (abs x) := 
by rw [←infinite_pos_iff_infinite_of_nonneg (abs_nonneg _), infinite_iff_infinite_pos_abs]

lemma infinite_iff_abs_lt_abs {x : ℝ*} : infinite x ↔ ∀ r : ℝ, (abs r : ℝ*) < abs x := sorry

lemma infinite_pos_add_not_infinite_neg {x y : ℝ*} : infinite_pos x → ¬ infinite_neg y → infinite_pos (x + y) := sorry

lemma not_infinite_neg_add_infinite_pos {x y : ℝ*} : ¬ infinite_neg x → infinite_pos y → infinite_pos (x + y) := 
λ hx hy, by rw [add_comm]; exact infinite_pos_add_not_infinite_neg hy hx

lemma infinite_neg_add_not_infinite_pos {x y : ℝ*} : infinite_neg x → ¬ infinite_pos y → infinite_neg (x + y) := sorry

lemma not_infinite_pos_add_infinite_neg {x y : ℝ*} : ¬ infinite_pos x → infinite_neg y → infinite_neg (x + y) := 
λ hx hy, by rw [add_comm]; exact infinite_neg_add_not_infinite_pos hy hx

lemma infinite_pos_add_infinite_pos {x y : ℝ*} : infinite_pos x → infinite_pos y → infinite_pos (x + y) := 
λ hx hy, infinite_pos_add_not_infinite_neg hx (not_infinite_neg_of_infinite_pos hy)

lemma infinite_neg_add_infinite_neg {x y : ℝ*} : infinite_neg x → infinite_neg y → infinite_neg (x + y) := 
λ hx hy, infinite_neg_add_not_infinite_pos hx (not_infinite_pos_of_infinite_neg hy)

lemma infinite_pos_add_not_infinite {x y : ℝ*} : infinite_pos x → ¬ infinite y → infinite_pos (x + y) := 
λ hx hy, infinite_pos_add_not_infinite_neg hx (not_or_distrib.mp hy).2

lemma infinite_neg_add_not_infinite {x y : ℝ*} : infinite_neg x → ¬ infinite y → infinite_neg (x + y) := 
λ hx hy, infinite_neg_add_not_infinite_pos hx (not_or_distrib.mp hy).1

lemma infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos {x y : ℝ*} : 
  infinite_pos x → ¬ infinitesimal y → y > 0 → infinite_pos (x * y) := sorry

lemma infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos {x y : ℝ*} : 
  ¬ infinitesimal x → x > 0 → infinite_pos y → infinite_pos (x * y) := 
λ hx hp hy, by rw [mul_comm]; exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hy hx hp

lemma infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg {x y : ℝ*} : 
  infinite_neg x → ¬ infinitesimal y → y < 0 → infinite_pos (x * y) := sorry

lemma infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg {x y : ℝ*} : 
  ¬ infinitesimal x → x < 0 → infinite_neg y → infinite_pos (x * y) := 
λ hx hp hy, by rw [mul_comm]; exact infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hy hx hp

lemma infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg {x y : ℝ*} : 
  infinite_pos x → ¬ infinitesimal y → y < 0 → infinite_neg (x * y) := sorry

lemma infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos {x y : ℝ*} : 
  ¬ infinitesimal x → x < 0 → infinite_pos y → infinite_neg (x * y) := 
λ hx hp hy, by rw [mul_comm]; exact infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hy hx hp

lemma infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos {x y : ℝ*} : 
  infinite_neg x → ¬ infinitesimal y → y > 0 → infinite_neg (x * y) := sorry

lemma infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg {x y : ℝ*} : 
  ¬ infinitesimal x → x > 0 → infinite_neg y → infinite_neg (x * y) := 
λ hx hp hy, by rw [mul_comm]; exact infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hy hx hp

lemma infinite_pos_mul_infinite_pos {x y : ℝ*} : infinite_pos x → infinite_pos y → infinite_pos (x * y) := 
λ hx hy, infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hx (not_infinitesimal_of_infinite_pos hy) (hy 0)

lemma infinite_neg_mul_infinite_neg {x y : ℝ*} : infinite_neg x → infinite_neg y → infinite_pos (x * y) := 
λ hx hy, infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hx (not_infinitesimal_of_infinite_neg hy) (hy 0)

lemma infinite_pos_mul_infinite_neg {x y : ℝ*} : infinite_pos x → infinite_neg y → infinite_neg (x * y) := 
λ hx hy, infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hx (not_infinitesimal_of_infinite_neg hy) (hy 0)

lemma infinite_neg_mul_infinite_pos {x y : ℝ*} : infinite_neg x → infinite_pos y → infinite_neg (x * y) := 
λ hx hy, infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hx (not_infinitesimal_of_infinite_pos hy) (hy 0)

lemma infinite_mul_of_infinite_not_infinitesimal {x y : ℝ*} : infinite x → ¬ infinitesimal y → infinite (x * y) := 
λ hx hy, have h0 : y < 0 ∨ y > 0 := lt_or_gt_of_ne (λ H0, hy (eq.substr H0 (is_st_refl_real 0))),
or.dcases_on hx
  (or.dcases_on h0 
    (λ H0 Hx, or.inr (infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg Hx hy H0))
    (λ H0 Hx, or.inl (infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos Hx hy H0))) 
  (or.dcases_on h0 
    (λ H0 Hx, or.inl (infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg Hx hy H0)) 
    (λ H0 Hx, or.inr (infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos Hx hy H0)))

lemma infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} : ¬ infinitesimal x → infinite y → infinite (x * y) := 
λ hx hy, by rw [mul_comm]; exact infinite_mul_of_infinite_not_infinitesimal hy hx

lemma infinite_mul_infinite {x y : ℝ*} : infinite x → infinite y → infinite (x * y) := 
λ hx hy, infinite_mul_of_infinite_not_infinitesimal hx (not_infinitesimal_of_infinite hy)

theorem infinite_pos_of_tendsto_top {f : ℕ → ℝ} (hf : tendsto f at_top at_top) : infinite_pos (of_seq f) := 
λ r, have hf' : _ := (tendsto_at_top_at_top (λ x y, ⟨max x y, ⟨le_max_left _ _, le_max_right _ _⟩⟩) _).mp hf,
Exists.cases_on (hf' (r + 1)) $ λ i hi,
  have hi' : ∀ (a : ℕ), f a < (r + 1) → a < i := λ a, by rw [←not_le, ←not_le]; exact not_imp_not.mpr (hi a),
  have hS : - {a : ℕ | r < f a} ⊆ {a : ℕ | a ≤ i} := 
  by simp only [set.compl_set_of, not_lt]; exact λ a har, le_of_lt (hi' a (lt_of_le_of_lt har (lt_add_one _))),
  (lt_def U).mpr $ mem_hyperfilter_of_finite_compl set.infinite_univ_nat $ set.finite_subset (set.finite_le_nat _) hS

theorem infinite_neg_of_tendsto_bot {f : ℕ → ℝ} (hf : tendsto f at_top at_bot) : infinite_neg (of_seq f) := 
λ r, have hf' : _ := (tendsto_at_top_at_bot _).mp hf,
Exists.cases_on (hf' (r - 1)) $ λ i hi,
  have hi' : ∀ (a : ℕ), r - 1 < f a → a < i := λ a, by rw [←not_le, ←not_le]; exact not_imp_not.mpr (hi a),
  have hS : - {a : ℕ | f a < r} ⊆ {a : ℕ | a ≤ i} := 
  by simp only [set.compl_set_of, not_lt]; exact λ a har, le_of_lt (hi' a (lt_of_lt_of_le (sub_one_lt _) har)),
  (lt_def U).mpr $ mem_hyperfilter_of_finite_compl set.infinite_univ_nat $ set.finite_subset (set.finite_le_nat _) hS

lemma infinite_pos_iff_infinite_neg_neg {x : ℝ*} : infinite_pos x ↔ infinite_neg (-x) := sorry

lemma infinite_neg_iff_infinite_pos_neg {x : ℝ*} : infinite_neg x ↔ infinite_pos (-x) := sorry

lemma infinite_iff_infinite_neg {x : ℝ*} : infinite x ↔ infinite (-x) := sorry

lemma not_infinite_add {x y : ℝ*} (hx : ¬ infinite x) (hy : ¬ infinite y) : ¬ infinite (x + y) := 
begin
  rw [infinite, not_or_distrib, infinite_pos, infinite_neg, not_forall, not_forall] at hx hy ⊢,
  rcases hx with ⟨⟨xr, hxr⟩, ⟨xl, hxl⟩⟩,
  rcases hy with ⟨⟨yr, hyr⟩, ⟨yl, hyl⟩⟩,
  simp only [not_lt] at hxl hxr hyl hyr ⊢, 
  exact ⟨⟨xr + yr, add_le_add hxr hyr⟩, ⟨xl + yl, add_le_add hxl hyl⟩⟩,
end

lemma not_infinite_neg {x : ℝ*} (hx : ¬ infinite x) : ¬ infinite (-x) := sorry

lemma not_infinite_mul {x y : ℝ*} (hx : ¬ infinite x) (hy : ¬ infinite y) : ¬ infinite (x * y) := sorry

theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬ infinite x ↔ ∃ r s : ℝ, ↑r < x ∧ x < s := sorry

theorem not_infinite_real (r : ℝ) : ¬ infinite r := by rw not_infinite_iff_exist_lt_gt; exact
⟨ r - 1, r + 1, 
  by rw [←of_eq_coe, ←of_eq_coe, ←of_lt U]; exact sub_one_lt _, 
  by rw [←of_eq_coe, ←of_eq_coe, ←of_lt U]; exact lt_add_one _⟩

theorem not_real_of_infinite {x : ℝ*} : infinite x → ∀ r : ℝ, x ≠ of r := sorry

-- FACTS ABOUT ST THAT REQUIRE SOME INFINITE MACHINERY

-- This isn't right
-- Perhaps f needs to be continuous?
/-lemma is_st_function {f : ℝ → ℝ} {x : ℝ*} {r : ℝ} : is_st x r → is_st ((lift f) x) (f r) := sorry

lemma is_st_function₂ {f : ℝ → ℝ → ℝ} {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st ((lift₂ f) x y) (f r s) := sorry

lemma st_function {f : ℝ → ℝ} (x : ℝ*) : (st ((lift f) x) : ℝ*) = (lift f) (st x : ℝ*) := sorry

lemma st_function₂ {f : ℝ → ℝ → ℝ} (x y : ℝ*) : (st ((lift₂ f) x y) : ℝ*) = (lift₂ f) (st x : ℝ*) (st y : ℝ*) := sorry-/

lemma is_st_add {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st (x + y) (r + s) := sorry

lemma st_add {x y : ℝ*} (hx : ¬infinite x) (hy : ¬infinite y) : st (x + y) = st x + st y := 
have hx' : _ := is_st_st' hx, 
have hy' : _ := is_st_st' hy,
have hxy : _ := is_st_st' (not_infinite_add hx hy),
have hxy' : _ := is_st_add hx' hy',
is_st_unique hxy hxy'

lemma is_st_neg {x : ℝ*} {r : ℝ} : is_st x r → is_st (-x) (-r) := sorry

lemma st_neg (x : ℝ*) : st (-x) = - st x := 
if h : infinite x then by rw [st_infinite h, st_infinite (infinite_iff_infinite_neg.mp h), neg_zero]
else is_st_unique (is_st_st' (not_infinite_neg h)) (is_st_neg (is_st_st' h))

lemma is_st_mul {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st (x * y) (r * s) := sorry

lemma st_mul {x y : ℝ*} (hx : ¬infinite x) (hy : ¬infinite y) : st (x * y) = (st x) * (st y) := 
have hx' : _ := is_st_st' hx, 
have hy' : _ := is_st_st' hy,
have hxy : _ := is_st_st' (not_infinite_mul hx hy),
have hxy' : _ := is_st_mul hx' hy',
is_st_unique hxy hxy'

lemma is_st_inv {x : ℝ*} {r : ℝ} (hi : ¬ infinitesimal x) : is_st x r → is_st x⁻¹ r⁻¹ := sorry

/- (st x < st y) → (x < y) → (x ≤ y) → (st x ≤ st y) -/

lemma is_st_le_of_lt {x y : ℝ*} {r s : ℝ} (hxr : is_st x r) (hsy : is_st y s) :
  x ≤ y → r ≤ s := sorry

lemma lt_of_is_st_lt {x y : ℝ*} {r s : ℝ} (hxr : is_st x r) (hsy : is_st y s) :
  r < s → x < y := sorry

lemma st_le_of_lt {x y : ℝ*} (hix : ¬ infinite x) (hiy : ¬ infinite y) : 
  x ≤ y → st x ≤ st y := sorry

lemma lt_of_st_lt {x y : ℝ*} (hix : ¬ infinite x) (hiy : ¬ infinite y) : 
  st x < st y → x < y := sorry

-- BASIC LEMMAS ABOUT INFINITESIMAL

theorem infinitesimal_def {x : ℝ*} : infinitesimal x ↔ (∀ r : ℝ, r > 0 → -(r : ℝ*) < x ∧ x < r) := 
⟨ λ hi r hr, by { convert (hi r hr), exact (zero_sub ↑r).symm, exact (zero_add ↑r).symm }, 
  λ hi d hd, by { convert (hi d hd), exact zero_sub ↑d, exact zero_add ↑d } ⟩

theorem lt_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, r > 0 → x < r := 
λ hi r hr, ((infinitesimal_def.mp hi) r hr).2

theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, r > 0 → x > -r := 
λ hi r hr, ((infinitesimal_def.mp hi) r hr).1

theorem gt_of_neg_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, r < 0 → x > r := 
λ hi r hr, by convert ((infinitesimal_def.mp hi) (-r) (neg_pos.mpr hr)).1; exact (neg_neg ↑r).symm

theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → abs x < abs r := 
⟨ λ hi r hr, have hi' : _ := infinitesimal_def.mp hi, begin
  cases (lt_or_gt_of_ne hr), sorry, sorry
end, sorry⟩ 

lemma infinitesimal_zero : infinitesimal 0 := is_st_refl_real 0

lemma zero_of_infinitesimal_real {r : ℝ} : infinitesimal r → r = 0 := eq_of_is_st_real

lemma zero_iff_infinitesimal_real {r : ℝ} : infinitesimal r ↔ r = 0 := 
⟨zero_of_infinitesimal_real, λ hr, by rw hr; exact infinitesimal_zero⟩

lemma infinitesimal_add {x y : ℝ*} : infinitesimal x → infinitesimal y → infinitesimal (x + y) := zero_add 0 ▸ is_st_add

lemma infinitesimal_neg {x : ℝ*} : infinitesimal x → infinitesimal (-x) := (neg_zero : -(0 : ℝ) = 0) ▸ is_st_neg

lemma infinitesimal_neg_iff {x : ℝ*} : infinitesimal x ↔ infinitesimal (-x) := 
⟨infinitesimal_neg, λ h, (neg_neg x) ▸ @infinitesimal_neg (-x) h⟩

lemma infinitesimal_mul {x y : ℝ*} : infinitesimal x → infinitesimal y → infinitesimal (x * y) := zero_mul 0 ▸ is_st_mul

theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} :
  tendsto f at_top (nhds 0) → infinitesimal (of_seq f) :=
λ hf d hd, by rw [←of_eq_coe, ←of_eq_coe, sub_eq_add_neg, ←of_neg, ←of_add, ←of_add, zero_add, zero_add, of_eq_coe, of_eq_coe];
exact ⟨neg_lt_of_tendsto_zero_of_neg hf hd, lt_of_tendsto_zero_of_pos hf hd⟩

theorem infinitesimal_epsilon : infinitesimal ε := infinitesimal_of_tendsto_zero tendsto_inverse_at_top_nhds_0_nat

lemma not_real_of_infinitesimal_ne_zero (x : ℝ*) : infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ of r := 
λ hi hx r hr, hx (is_st_unique (hr.symm ▸ is_st_refl_real r : is_st x r) hi ▸ hr : x = of 0)

theorem infinitesimal_sub_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r): infinitesimal (x - r) := 
show is_st (x + -r) 0, by rw ←add_neg_self r; exact is_st_add hxr (is_st_refl_real (-r))

theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬infinite x) : infinitesimal (x - st x) := 
infinitesimal_sub_is_st $ is_st_st' hx

lemma infinite_pos_iff_infinitesimal_inv_pos {x : ℝ*} : infinite_pos x ↔ (infinitesimal x⁻¹ ∧ x⁻¹ > 0) := sorry

lemma infinite_neg_iff_infinitesimal_inv_neg {x : ℝ*} : infinite_neg x ↔ (infinitesimal x⁻¹ ∧ x⁻¹ < 0) := 
⟨ λ hin, have hin' : _ := infinite_pos_iff_infinitesimal_inv_pos.mp (infinite_pos_neg_of_infinite_neg hin),
 by rwa [infinitesimal_neg_iff, ←neg_pos, neg_inv (λ h0, lt_irrefl x (by convert hin 0) : x ≠ 0)], 
 λ hin, have h0 : x ≠ 0 := λ h0, (lt_irrefl (0 : ℝ*) (by convert hin.2; rw [h0, inv_zero])),
 by rwa [←neg_pos, infinitesimal_neg_iff, neg_inv h0, ←infinite_pos_iff_infinitesimal_inv_pos, ←infinite_pos_neg_iff_infinite_neg] at hin ⟩ 

theorem infinitesimal_inv_of_infinite {x : ℝ*} : infinite x → infinitesimal x⁻¹ := 
λ hi, or.cases_on hi 
 (λ hip, (infinite_pos_iff_infinitesimal_inv_pos.mp hip).1) 
 (λ hin, (infinite_neg_iff_infinitesimal_inv_neg.mp hin).1)

theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : infinitesimal x⁻¹ ) : infinite x :=
begin 
  cases (lt_or_gt_of_ne h0) with hn hp,
  { exact or.inr (infinite_neg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_neg'.mpr hn⟩) },
  { exact or.inl (infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos'.mpr hp⟩) }
end

theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : infinite x ↔ infinitesimal x⁻¹ := 
⟨ infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0 ⟩ 

lemma infinitesimal_pos_iff_infinite_pos_inv {x : ℝ*} : infinite_pos x⁻¹ ↔ (infinitesimal x ∧ x > 0) := 
begin
  convert infinite_pos_iff_infinitesimal_inv_pos,
  all_goals { by_cases h : x = 0,
    rw [h, inv_zero, inv_zero],
    exact (division_ring.inv_inv h).symm }
end

lemma infinitesimal_neg_iff_infinite_neg_inv {x : ℝ*} : infinite_neg x⁻¹ ↔ (infinitesimal x ∧ x < 0) := 
begin
  convert infinite_neg_iff_infinitesimal_inv_neg,
  all_goals { by_cases h : x = 0,
    rw [h, inv_zero, inv_zero],
    exact (division_ring.inv_inv h).symm }
end

theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : infinitesimal x ↔ infinite x⁻¹ := 
begin
  convert (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm,
  exact (division_ring.inv_inv h).symm
end

-- ST STUFF THAT REQUIRES INFINITESIMAL MACHINERY

theorem is_st_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : tendsto f at_top (nhds r)) :
  is_st (of_seq f) r :=
have hg : tendsto (λ n, f n - r) at_top (nhds 0) := (sub_self r) ▸ (tendsto_sub hf tendsto_const_nhds),
by rw [←(zero_add r), ←(sub_add_cancel f (λ n, r))]; 
exact is_st_add (infinitesimal_of_tendsto_zero hg) (is_st_refl_real r)

lemma st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ := 
begin
  by_cases h0 : x = 0,
  rw [h0, inv_zero, ←of_zero, of_eq_coe, st_id_real, inv_zero],
  by_cases h1 : infinitesimal x,
  rw [st_infinite ((infinitesimal_iff_infinite_inv h0).mp h1), st_of_is_st h1, inv_zero],
  by_cases h2 : infinite x,
  rw [st_of_is_st (infinitesimal_inv_of_infinite h2), st_infinite h2, inv_zero],
  exact st_of_is_st (is_st_inv h1 (is_st_st' h2)),
end

-- INFINITE STUFF THAT REQUIRES INFINITESIMAL MACHINERY

lemma infinite_pos_omega : infinite_pos ω := 
infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

lemma infinite_omega : infinite ω := (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

end hyperreal