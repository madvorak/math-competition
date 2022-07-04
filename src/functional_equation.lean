import data.real.nnreal


theorem must_be_identity {f : nnreal → nnreal} (h : ∀ x y : nnreal,
      f (f x + (y + 1) / (f y)) = 1 / (f y) + x + 1) :
  ∀ x : nnreal,  x > 0  →  f x = x  :=
begin
  let A : nnreal := 1 / f 1 + 1,
  have high_range : ∀ B : nnreal, B > A → (∃ z : nnreal, f z = B),
  {
    intros B B_gt_A,
    let x := B - A,
    have equ := h x 1,
    use f x + 2 / f 1,
    rw one_add_one_eq_two at equ,
    rw equ,
    change 1 / f 1 + (B - (1 / f 1 + 1)) + 1 = B,
    --have xpos : B - (1 / f 1 + 1) > 0, sorry,
    convert_to 1 / f 1 + B - (1 / f 1 + 1) + 1 = B, sorry,
    convert_to 1 / f 1 + B - (1 / f 1) - 1 + 1 = B, sorry,
    convert_to 1 / f 1 + B - (1 / f 1) + 1 - 1 = B, sorry,
    convert_to 1 / f 1 + B - (1 / f 1) + 0 = B, sorry,
    convert_to 1 / f 1 + B - (1 / f 1) = B, rw add_zero,
    finish,
  },
  have inj_f : function.injective f,
  {
    intros a b fa_eq_fb,
    have foo : ∀ c : nnreal, 1 / (f c) + a + 1 = 1 / (f c) + b + 1,
    {
      intro c,
      rw ← h a c,
      rw ← h b c,
      rw fa_eq_fb,
    },
    finish,
  },

  have lin_on_rat : ∀ p q : ℕ, let x : nnreal := ↑p / ↑q in
      f x = f 1 + (x - 1) * (f 2 - f 1),
  {
    intros p q,
    sorry,
  },
  have increasing_f :  ∀ x y : nnreal,  x < y  →  f x < f y,
  {
    sorry,
  },
  have lin_on_real : ∀ x : nnreal, f x = f 1 + (x - 1) * (f 2 - f 1),
  {
    intro x,
    sorry,
  },

  have degree_one : ∃ a b : nnreal, ∀ x : nnreal, f x = a * x + b,
  {
    use f 2 - f 1,
    use f 1 + f 1 - f 2,
    intro x,
    rw lin_on_real x,
    sorry,
  },
  rcases degree_one with ⟨a, b, hf⟩,
  intros x xpos,

  have a_eq_1 : a = 1,
  {
    specialize h x 42,
    rw hf x at h,
    rw hf 42 at h,
    rw hf (a * x + b + (42 + 1) / (a * 42 + b)) at h,
    ring_nf at h,
    sorry,
  },
  have b_eq_0 : b = 0,
  {
    sorry,
  },
  rw hf x,
  rw a_eq_1,
  rw b_eq_0,
  rw add_zero,
  rw one_mul,
end
