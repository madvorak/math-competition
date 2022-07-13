import data.real.basic

lemma eq_of_arbitrarily_close :
  ∀ x y : ℝ, (∀ ε : ℝ, ε > 0 → |y - x| < ε) → x = y :=
begin
  intros x y arbitrarily_close,
  by_contradiction,
  have false_of_abs_lt : ∀ a : ℝ, |a| < a → false,
  {
    intros a abs_lt,
    have lt_self : a < a, exact lt_of_abs_lt abs_lt,
    have ne_self : a ≠ a, exact ne_of_lt lt_self,
    exact false_of_ne ne_self,
  },
  cases lt_or_gt_of_ne h with case_lt case_gt,
  {
    rw ← sub_pos at case_lt,
    specialize arbitrarily_close (y - x) case_lt,
    exact false_of_abs_lt (y - x) arbitrarily_close,
  },
  {
    change y < x at case_gt,
    rw ← sub_pos at case_gt,
    specialize arbitrarily_close (x - y) case_gt,
    rw abs_sub_comm y x at arbitrarily_close,
    exact false_of_abs_lt (x - y) arbitrarily_close,
  },
end

lemma min__div {a b c : ℝ} (c_pos : c > 0) :
  (min a b) / c = min (a / c) (b / c) :=
begin
  unfold min,
  unfold min_default,
  split_ifs with hab habc habc,
  {
    refl,
  },
  {
    exfalso,
    rw ← div_le_div_right c_pos at hab,
    exact habc hab,
  },
  {
    exfalso,
    rw div_le_div_right c_pos at habc,
    exact hab habc,
  },
  {
    refl,
  },
end

lemma mul__div_div {a b c : ℝ} (c_pos : c > 0) : a * (c / b / c) = a / b :=
begin
  have hc : c ≠ 0, exact ne_of_gt c_pos,
  have almost : c / b / c = 1 / b,
  {
    ring_nf,
    rw mul_comm,
    rw ← mul_assoc,
    rw mul_inv_cancel hc,
    rw one_mul,
  },
  rw almost,
  exact mul_one_div a b,
end

lemma lin_on_real {f : ℝ → ℝ}
  (increasing : ∀ x y : ℝ,  0 < x  →  x < y  →  f x < f y)
  (lin_on_rat : ∀ x : ℚ,  0 < x  →  f x = f 1 + (x - 1) * (f 2 - f 1)
  ) :           ∀ x : ℝ,  0 < x  →  f x = f 1 + (x - 1) * (f 2 - f 1)  :=
begin
  have lt_f2_f1 : 0 < f 2 - f 1,
  {
    rw sub_pos,
    exact increasing _ _ one_pos one_lt_two,
  },
  intros x x_pos,
  have ex₁ : ∀ ε : ℝ, ε > 0 → ∃ x₁ : ℚ,
    ↑x₁ < x  ∧  x - ↑x₁ < ε / (f 2 - f 1),
  {
    intros ε ε_pos,
    have that_pos : ε / (f 2 - f 1) > 0,
    {
      exact div_pos ε_pos lt_f2_f1,
    },
    rcases exists_rat_btwn (sub_lt_self x that_pos) with ⟨x₁, below, above⟩,
    use x₁,
    split,
    {
      exact above,
    },
    {
      rw sub_lt,
      exact below,
    },
  },
  have ex₂ : ∀ ε : ℝ, ε > 0 → ∃ x₂ : ℚ,
    x < ↑x₂  ∧  ↑x₂ - x < ε / (f 2 - f 1),
  {
    intros ε ε_pos,
    have that_pos : ε / (f 2 - f 1) > 0,
    {
      exact div_pos ε_pos lt_f2_f1,
    },
    rcases exists_rat_btwn (lt_add_of_pos_right x that_pos) with ⟨x₂, below, above⟩,
    use x₂,
    split,
    {
      exact below,
    },
    {
      rw sub_lt_iff_lt_add',
      exact above,
    },
  },
  apply eq_of_arbitrarily_close,
  intros ε ε_pos,
  cases ex₁ ((min ε (x * (f 2 - f 1) / 2))) (by {
    change 0 < min ε (x * (f 2 - f 1) / 2),
    rw lt_min_iff,
    split,
    {
      exact ε_pos,
    },
    {
      apply half_pos,
      exact mul_pos x_pos lt_f2_f1,
    },
  }) with x₁ hx₁,
  cases hx₁ with x₁_lt_x dist₁,
  rw min__div lt_f2_f1 at dist₁,
  have x₁_pos : 0 < (x₁ : ℝ),
  {
    rw lt_min_iff at dist₁,
    cases dist₁ with foo bar,
    have baz : x - ↑x₁ < x / 2,
    {
      rw mul_div_assoc at bar,
      rw mul_div_assoc at bar,
      convert bar,
      rw mul__div_div lt_f2_f1,
    },
    have qux : x / 2 < ↑x₁,
    {
      clear_except baz,
      linarith,
    },
    apply lt_trans' qux,
    exact half_pos x_pos,
  },
  have fx₁ := lin_on_rat x₁ (by {
    clear_except x₁_pos,
    assumption_mod_cast,
  }),
  cases ex₂ ε ε_pos with x₂ hx₂,
  cases hx₂ with x_lt_x₂ dist₂,
  have fx₂ := lin_on_rat x₂ (by {
    have x₂_pos := lt_trans x_pos x_lt_x₂,
    clear_except x₂_pos,
    assumption_mod_cast,
  }),
  have inc₁ := increasing ↑x₁ x x₁_pos x₁_lt_x,
  have inc₂ := increasing x  ↑x₂ x_pos x_lt_x₂,
  rw fx₁ at inc₁,
  rw fx₂ at inc₂,
  rw abs_lt,
  split,
  {
    rw lt_sub,
    apply lt_trans inc₂,
    rw sub_neg_eq_add,
    rw add_assoc,
    rw add_lt_add_iff_left,
    rw sub_mul,
    rw sub_mul,
    rw sub_add_comm,
    rw add_comm,
    rw ← add_sub_assoc,
    rw sub_lt_sub_iff_right,
    rw ← sub_lt_iff_lt_add',
    rw ← sub_mul,
    rw ← lt_div_iff lt_f2_f1,
    exact dist₂,
  },
  {
    have intermediate_ineq :
      f 1 + (x - 1) * (f 2 - f 1) - f x <
      f 1 + (x - 1) * (f 2 - f 1) - (f 1 + (↑x₁ - 1) * (f 2 - f 1)),
    {
      exact sub_lt_sub_left inc₁ (f 1 + (x - 1) * (f 2 - f 1)),
    },
    apply lt_trans intermediate_ineq,
    rw sub_mul,
    rw sub_mul,
    rw add_sub_add_left_eq_sub,
    rw sub_sub_sub_cancel_right,
    rw ← sub_mul,
    rw ← lt_div_iff lt_f2_f1,
    {
      clear_except dist₁,
      finish,
    },
  },
end

theorem must_be_identity {f : ℝ → ℝ} (codomain : ∀ x : ℝ, f x > 0)
    (h : ∀ x y : ℝ, f (f x + (y + 1) / (f y)) = 1 / (f y) + x + 1) :
  ∀ x : ℝ,  x > 0  →  f x = x  :=
begin
  let A : ℝ := 1 / f 1 + 1,
  have high_range : ∀ B : ℝ, B > A → (∃ z : ℝ, f z = B),
  {
    intros B B_gt_A,
    let x := B - A,
    have equ := h x 1,
    use f x + 2 / f 1,
    rw one_add_one_eq_two at equ,
    rw equ,
    change 1 / f 1 + (B - (1 / f 1 + 1)) + 1 = B,
    ring,
  },
  have inj_f : function.injective f,
  {
    intros a b fa_eq_fb,
    have foo : ∀ c : ℝ, 1 / (f c) + a + 1 = 1 / (f c) + b + 1,
    {
      intro c,
      rw ← h a c,
      rw ← h b c,
      rw fa_eq_fb,
    },
    finish,
  },
  have f_increment :
    ∀ δ : ℝ, (0 < δ ∧ δ < 1 / A) → ∃ ε : ℝ,
      ∀ x : ℝ, x > 0 → f (x + δ) = f x + ε,
  {
    intros δ restrictions,
    have delta_inv_pos : 0 < 1 / δ, exact one_div_pos.mpr restrictions.1,
    have f1_inv_pos : 1 / f 1 > 0, exact one_div_pos.mpr (codomain 1),

    let B := (A + 1 / δ) / 2,
    let C := (A + 1 / δ) * (1 / δ) / ((1 / δ) - A),
    have delta_eq : δ = 1 / B - 1 / C,
    {
      change δ = 1 / ((A + 1 / δ) / 2) - 1 / ((A + 1 / δ) * (1 / δ) / ((1 / δ) - A)),
      rw one_div_div,
      rw one_div_div,
      symmetry,
      have positiv : A + 1 / δ > 0,
      {
        change 1 / f 1 + 1 + 1 / δ > 0,
        linarith,
      },
      calc 2 / (A + 1 / δ) - (1 / δ - A) / ((A + 1 / δ) * (1 / δ))
          = (2 * (1 / δ)) / ((A + 1 / δ) * (1 / δ)) - (1 / δ - A) / ((A + 1 / δ) * (1 / δ)) :
            by rw mul_div_mul_right _ _ (ne_of_gt (one_div_pos.mpr restrictions.1))
      ... = (2 * (1 / δ) - (1 / δ - A)) / ((A + 1 / δ) * (1 / δ)) : by rw div_sub_div_same
      ... = ((1 / δ) + A) / ((A + 1 / δ) * (1 / δ))               : by ring
      ... = (A + 1 / δ) / ((A + 1 / δ) * (1 / δ))                 : by rw add_comm
      ... = ((A + 1 / δ) / (A + 1 / δ)) / (1 / δ)                 : by rw div_div
      ... = 1 / (1 / δ)                                           : by rw div_self (ne_of_gt positiv)
      ... = δ                                                     : by rw one_div_one_div,
    },
    have A_pos : A > 0,
    {
      change 1 / f 1 + 1 > 0,
      specialize codomain 1,
      linarith,
    },
    have A_lt_delta_inv : A < 1 / δ,
    {
      exact (lt_one_div restrictions.1 A_pos).mp restrictions.2,
    },
    have B_gt_A : B > A,
    {
      change (A + 1 / δ) / 2 > A,
      linarith,
    },
    have C_gt_B : C > B,
    {
      have is_pos := restrictions.1,
      have inv_ineq : 1 / C < 1 / B,
      {
        rw delta_eq at is_pos,
        exact sub_pos.mp is_pos,
      },
      have B_pos : B > 0, exact gt_trans B_gt_A A_pos,
      have C_pos : C > 0,
      {
        apply mul_pos,
        apply mul_pos,
        {
          exact add_pos A_pos delta_inv_pos,
        },
        {
          rw one_div_pos,
          exact is_pos,
        },
        {
          rw inv_pos,
          rw sub_pos,
          exact A_lt_delta_inv,
        },
      },
      exact (one_div_lt_one_div C_pos B_pos).mp inv_ineq,
    },
    obtain ⟨y₁, preimage_B⟩ : ∃ y₁ : ℝ, f y₁ = B,
    {
      exact high_range B B_gt_A,
    },
    obtain ⟨y₂, preimage_C⟩ : ∃ y₂ : ℝ, f y₂ = C,
    {
      exact high_range C (gt_trans C_gt_B B_gt_A),
    },
    have equ : ∀ x : ℝ, x > 0 → 1 / f y₁ + x + 1 = 1 / f y₂ + (x+δ) + 1,
    {
      intros x x_pos,
      rw delta_eq,
      rw preimage_B,
      rw preimage_C,
      ring,
    },
    have henc : ∀ x : ℝ, x > 0 → f (f x + (y₁ + 1) / (f y₁)) = f (f (x+δ) + (y₂ + 1) / (f y₂)),
    {
      intros x x_pos,
      rw h x y₁,
      rw h (x+δ) y₂,
      rw delta_eq,
      rw preimage_B,
      rw preimage_C,
      ring,
    },
    have by_inj : ∀ x : ℝ, x > 0 → f x + (y₁ + 1) / (f y₁) = f (x+δ) + (y₂ + 1) / (f y₂),
    {
      intros x x_pos,
      exact inj_f (henc x x_pos),
    },
    use (y₁ + 1) / (f y₁) - (y₂ + 1) / (f y₂),
    intros x x_pos,
    sorry,
  },
  have f_multiple_increment :
    ∀ δ : ℝ, (0 < δ ∧ δ < 1 / A) → ∃ ε : ℝ,
      ∀ x : ℝ, x > 0 → ∀ n : ℕ, f (x + n * δ) = f x + n * ε,
  {
    intros δ restrictions,
    obtain ⟨ε, step⟩ := f_increment δ restrictions,
    use ε,
    intros x x_pos n,
    induction n with n ih,
    {
      simp,
    },
    convert_to f (x + ↑n * δ + δ) = f x + ↑n * ε + ε, sorry, sorry,
    rw ← ih,
    rw step,
    calc x + ↑n * δ ≥ x : by finish
    ... > 0 : x_pos,
  },
  have f_lin_on_rat : ∀ x : ℚ,  0 < x  →  f x = f 1 + (x - 1) * (f 2 - f 1),
  {
    intros x x_pos,
    sorry,
  },
  have f_increasing :  ∀ x y : ℝ,  0 < x  →  x < y  →  f x < f y,
  {
    sorry,
  },
  have f_lin_on_real : ∀ x : ℝ,  0 < x  →  f x = f 1 + (x - 1) * (f 2 - f 1),
  {
    exact lin_on_real f_increasing f_lin_on_rat,
  },

  have degree_one : ∃ a b : ℝ, ∀ x : ℝ,  0 < x  →  f x = a * x + b,
  {
    use f 2 - f 1,
    use f 1 + f 1 - f 2,
    intros x x_pos,
    rw f_lin_on_real x x_pos,
    ring,
  },
  rcases degree_one with ⟨a, b, hf⟩,
  have a_eq_1 : a = 1,
  {
    specialize h 1 1,
    repeat { rw hf 1 zero_lt_one at h },
    rw hf at h, swap, sorry,
    rw mul_one at h,
    rw mul_add at h,
    rw mul_add at h,
    have multiplied := congr_arg (λ v, (a + b) * v) h,
    dsimp at multiplied,
    rw mul_add (a + b) _ 1 at multiplied,
    rw mul_add (a + b) _ 1 at multiplied,
    rw mul_div (a + b) 1 (a + b) at multiplied,
    rw mul_comm (a + b) 1 at multiplied,
    repeat { rw one_mul at multiplied },
    have a_plus_b_neq_zero : a + b ≠ 0, sorry,
    rw div_self a_plus_b_neq_zero at multiplied,
    repeat { rw mul_add (a + b) at multiplied },
    rw ← mul_assoc (a + b) a ((1 + 1) / (a + b)) at multiplied,
    rw mul_div at multiplied,
    rw mul_comm (a + b) a at multiplied,
    rw mul_assoc at multiplied,
    rw mul_comm (a + b) (1 + 1) at multiplied,
    rw ← mul_div at multiplied,
    rw ← mul_div at multiplied,
    rw div_self a_plus_b_neq_zero at multiplied,
    rw mul_one at multiplied,
    have subtracted := congr_arg (λ v, v - 2 * a) multiplied,
    dsimp at subtracted,
    ring_nf at subtracted,
    sorry,
  },
  have b_eq_0 : b = 0,
  {
    rw a_eq_1 at hf,
    sorry,
  },

  intros x x_pos,
  rw hf x x_pos,
  rw a_eq_1,
  rw b_eq_0,
  rw add_zero,
  rw one_mul,
end
