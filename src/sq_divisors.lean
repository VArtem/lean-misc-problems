import number_theory.divisors
import data.fintype.basic
import tactic

/-
This file formalizes the following mathematical problem: 
"Given n, count the positive natural solutions to 1/a + 1/b = 1/n".
I show that the number of such solutions is equal to the number of divisors of n^2 through the explicit equivalence.
-/

def is_solution (n a b : ℕ) := a ≠ 0 ∧ b ≠ 0 ∧ (a : ℚ)⁻¹ + (b : ℚ)⁻¹ = (n : ℚ)⁻¹

@[simp] lemma is_solution_def {n a b} : 
  is_solution n a b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (a : ℚ)⁻¹ + (b : ℚ)⁻¹ = (n : ℚ)⁻¹ := iff.rfl

lemma n_ne_zero_of_is_solution {n a b} (h : is_solution n a b) :
  n ≠ 0 :=
begin
  rcases h with ⟨ha, hb, h⟩,
  have : (n : ℚ)⁻¹ > 0,
  { calc (n : ℚ)⁻¹ = (a : ℚ)⁻¹ + (b : ℚ)⁻¹  : h.symm
      ...          > 0 + 0                  : add_lt_add _ _
      ...          = 0                      : add_zero _,
      all_goals { rwa [inv_pos, nat.cast_pos, pos_iff_ne_zero] } },
  rwa [gt_iff_lt, inv_pos, nat.cast_pos, pos_iff_ne_zero] at this,
end

lemma is_solution_iff_aux {n a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hn : n ≠ 0) :
  (a : ℚ)⁻¹ + (b : ℚ)⁻¹ = (n : ℚ)⁻¹ ↔ (a + b) * n = a * b :=
begin
  rw @inv_add_inv ℚ _ _ _ (nat.cast_ne_zero.2 ha) (nat.cast_ne_zero.mpr hb),
  rw ←(mul_eq_one_iff_eq_inv₀ $ (@nat.cast_ne_zero ℚ _ _ _ _).2 hn),
  rw div_mul_eq_mul_div,
  rw div_eq_iff (@mul_ne_zero ℚ _ _ _ _ (nat.cast_ne_zero.2 ha) (nat.cast_ne_zero.2 hb)),
  rw one_mul,
  norm_cast,
end

lemma is_solution_mp {n a b : ℕ} (h : is_solution n a b) : 
  a ≠ 0 ∧ b ≠ 0 ∧ (a + b) * n = a * b :=
begin
  have hn := n_ne_zero_of_is_solution h,
  rcases h with ⟨ha, hb, h⟩,
  exact ⟨ha, hb, (is_solution_iff_aux ha hb hn).1 h⟩,
end

lemma is_solution_mpr {n a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : (a + b) * n = a * b) : 
  is_solution n a b :=
begin
  have hn : n ≠ 0 := by {rintro rfl, apply mul_ne_zero ha hb, simpa using h},
  exact ⟨ha, hb, (is_solution_iff_aux ha hb hn).2 h⟩,
end

lemma is_solution_iff {n a b : ℕ} :
  is_solution n a b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (a + b) * n = a * b :=
  ⟨is_solution_mp, λ ⟨ha, hb, h⟩, is_solution_mpr ha hb h⟩

lemma n_le_a_of_is_solution {n a b : ℕ} (h : is_solution n a b) : n ≤ a :=
begin
  replace h := is_solution_mp h,
  rcases h with ⟨ha, hb, h⟩,
  nlinarith [nat.pos_of_ne_zero ha, nat.pos_of_ne_zero hb],
end

lemma n_lt_a_of_is_solution {n a b : ℕ} (h : is_solution n a b) : n < a :=
begin
  replace h := is_solution_mp h,
  rcases h with ⟨ha, hb, h⟩,
  nlinarith [nat.pos_of_ne_zero ha, nat.pos_of_ne_zero hb],
end

lemma n_le_b_of_is_solution {n a b : ℕ} (h : is_solution n a b) : n ≤ b :=
begin
  replace h := is_solution_mp h,
  rcases h with ⟨ha, hb, h⟩,
  nlinarith [nat.pos_of_ne_zero ha, nat.pos_of_ne_zero hb],
end

lemma n_lt_b_of_is_solution {n a b : ℕ} (h : is_solution n a b) : n < b :=
begin
  replace h := is_solution_mp h,
  rcases h with ⟨ha, hb, h⟩,
  nlinarith [nat.pos_of_ne_zero ha, nat.pos_of_ne_zero hb],
end

def solutions (n : ℕ) : set (ℕ × ℕ) := { p | is_solution n p.1 p.2 }

def solutions_equiv_sq_divisors (n : ℕ) [h_ne_zero : fact (n ≠ 0)] : solutions n ≃ (n*n).divisors :=
  { to_fun := λ p, ⟨p.1.1 - n, 
  begin
    rcases p with ⟨⟨a, b⟩, hsol⟩,
    rw nat.mem_divisors,
    dsimp only,
    have n_le_a := n_le_a_of_is_solution hsol,
    have n_le_b := n_le_b_of_is_solution hsol,
    rw [solutions, set.mem_set_of, is_solution_iff] at hsol,
    dsimp [-ne.def] at hsol,
    refine ⟨⟨b - n, _⟩, mul_self_ne_zero.2 h_ne_zero.out⟩,
    zify [n_le_a, n_le_b] at hsol ⊢,
    rw [mul_sub, sub_mul, sub_mul],
    linarith,
  end⟩,
  inv_fun := λ d, { val := ⟨d.val + n, n*n/d.val + n⟩,
  property := 
  begin
    rcases d with ⟨d, h⟩,
    dsimp [solutions],
    rw nat.mem_divisors at h,
    rcases h with ⟨h_dvd, h_eq⟩,
    rw is_solution_iff,
    refine ⟨_, _, _⟩,
    { rw ←pos_iff_ne_zero, exact add_pos_of_nonneg_of_pos (zero_le _) (nat.pos_of_ne_zero h_ne_zero.out), },
    { rw ←pos_iff_ne_zero, exact add_pos_of_nonneg_of_pos (zero_le _) (nat.pos_of_ne_zero h_ne_zero.out), },
    have tmp : (n * n / d) * d = n * n := nat.div_mul_cancel h_dvd,
    linarith,
  end},
  left_inv := begin
    rintro ⟨⟨a, b⟩, hsol⟩,
    apply subtype.eq,
    dsimp only,
    rw [solutions, set.mem_set_of] at hsol,
    have n_le_a := n_le_a_of_is_solution hsol,
    have n_le_b := n_le_b_of_is_solution hsol,
    have n_lt_a := n_lt_a_of_is_solution hsol,
    have n_lt_b := n_lt_b_of_is_solution hsol,
    rw is_solution_iff at hsol,
    dsimp only at hsol,
    rcases hsol with ⟨ha, hb, hsol⟩,
    ext; dsimp at *,
    { exact nat.sub_add_cancel n_le_a, },
    { have n_lt_a : a - n > 0 := nat.sub_pos_of_lt n_lt_a,
      rw ←nat.add_mul_div_left _ _ n_lt_a,
      rw [nat.mul_sub_right_distrib, ←nat.add_sub_assoc (mul_le_mul_right' n_le_a n), add_comm (n * n) (a * n), nat.add_sub_cancel],
      apply nat.div_eq_of_eq_mul_left n_lt_a,
      linarith,
    },
  end,
  right_inv := begin
    rintro ⟨x, h_dvd⟩,
    apply subtype.eq,
    dsimp,
    exact nat.add_sub_cancel _ _,
  end }

instance solutions_fintype (n : ℕ) [h_ne_zero : fact (n ≠ 0)] : fintype (solutions n) := 
  fintype.of_equiv _ (solutions_equiv_sq_divisors n).symm

lemma solutions_count (n : ℕ) [h_ne_zero : fact (n ≠ 0)] : fintype.card (solutions n) = (n*n).divisors.card :=
begin
  rw fintype.of_equiv_card (solutions_equiv_sq_divisors n).symm,
  simp only [fintype.card_coe],
end

instance : fact (60 ≠ 0) := ⟨by norm_num⟩

#eval fintype.card ↥(solutions 60)
