import data.real.basic

theorem must_be_identity {f : ℝ → ℝ} (h : ∀ x y : ℝ,
      f (f x + (y + 1) / (f y)) = 1 / (f y) + x + 1) :
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
        sorry,
      },
      calc 2 / (A + 1 / δ) - (1 / δ - A) / ((A + 1 / δ) * (1 / δ))
          = (2 * (1 / δ) - (1 / δ - A)) / ((A + 1 / δ) * (1 / δ)) : sorry
      ... = ((1 / δ) + A) / ((A + 1 / δ) * (1 / δ))               : by ring
      ... = (A + 1 / δ) / ((A + 1 / δ) * (1 / δ))                 : by rw add_comm
      ... = ((A + 1 / δ) / (A + 1 / δ)) / (1 / δ)                 : by rw div_div
      ... = 1 / (1 / δ)                                           : by rw div_self (ne_of_gt positiv)
      ... = δ                                                     : one_div_one_div δ,
    },
    obtain ⟨y₁, preimage_B⟩ : ∃ y₁ : ℝ, f y₁ = B,
    {
      exact high_range B sorry,
    },
    obtain ⟨y₂, preimage_C⟩ : ∃ y₂ : ℝ, f y₂ = C,
    {
      exact high_range C sorry,
    },
    have equ : ∀ x : ℝ, x > 0 → 1 / f y₁ + x + 1 = 1 / f y₂ + (x+δ) + 1, sorry,
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
    have byinj : ∀ x : ℝ, x > 0 → f x + (y₁ + 1) / (f y₁) = f (x+δ) + (y₂ + 1) / (f y₂),
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
  have lin_on_rat : ∀ p q : ℕ, let x : ℝ := ↑p / ↑q in
      f x = f 1 + (x - 1) * (f 2 - f 1),
  {
    intros p q,
    sorry,
  },
  have increasing_f :  ∀ x y : ℝ,  0 < x  →  x < y  →  f x < f y,
  {
    sorry,
  },
  have lin_on_real : ∀ x : ℝ, f x = f 1 + (x - 1) * (f 2 - f 1),
  {
    intro x,
    sorry,
  },

  have degree_one : ∃ a b : ℝ, ∀ x : ℝ, f x = a * x + b,
  {
    use f 2 - f 1,
    use f 1 + f 1 - f 2,
    intro x,
    rw lin_on_real x,
    ring,
  },
  rcases degree_one with ⟨a, b, hf⟩,
  have a_eq_1 : a = 1,
  {
    specialize h 1 1,
    repeat { rw hf at h },
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
    rw div_self at multiplied,
    repeat { rw mul_add (a + b) at multiplied },
    rw ← mul_assoc (a + b) a ((1 + 1) / (a + b)) at multiplied,
    rw mul_div at multiplied,
    rw mul_comm (a + b) a at multiplied,
    rw mul_assoc at multiplied,
    rw mul_comm (a + b) (1 + 1) at multiplied,
    rw ← mul_div at multiplied,
    rw ← mul_div at multiplied,
    rw div_self at multiplied,
    rw mul_one at multiplied,
    have subtracted := congr_arg (λ v, v - 2 * a) multiplied,
    dsimp at subtracted,
    ring_nf at subtracted,
    sorry, sorry, sorry,
  },
  have b_eq_0 : b = 0,
  {
    rw a_eq_1 at hf,
    sorry,
  },

  intros x xpos,
  rw hf x,
  rw a_eq_1,
  rw b_eq_0,
  rw add_zero,
  rw one_mul,
end
