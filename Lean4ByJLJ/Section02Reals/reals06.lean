import Mathlib.Tactic -- imports all the Lean tactics

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize h (ε / 37) (by linarith)
  cases' h with X hX
  use X
  intro n h
  specialize hX n h
  rw [← mul_sub]
  rw [abs_mul]
  rw [abs_of_nonneg]
  <;> linarith


/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  have hε_div_c : ε / c > 0 := div_pos hε hc
  specialize h (ε / c) (by linarith)
  cases' h with X hX
  use X
  intro n hn
  specialize hX n hn
  rw [← mul_sub]
  rw [abs_mul]
  rw [abs_of_nonneg]
  rw [mul_comm]
  exact (lt_div_iff₀ hc).mp hX
  linarith


/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  have hc' : 0 < -c := neg_pos.mpr hc
  have hε_div_c : ε / -c > 0 := div_pos hε hc'
  specialize h (ε / -c) (by linarith)
  cases' h with X hX
  use X
  intro n hn
  specialize hX n hn
  rw [← mul_sub]
  rw [abs_mul]
  rw [← abs_neg]
  rw [abs_of_nonneg]
  rw [mul_comm]
  exact (lt_div_iff₀ hc').mp hX
  linarith


/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    obtain hc | hc | hc := lt_trichotomy c 0
    exact tendsTo_neg_const_mul h hc
    rw [tendsTo_def] at *
    intro ε h2
    use 1
    intro n hn
    rw [hc]
    rw [zero_mul]
    simp
    exact h2
    exact tendsTo_pos_const_mul h hc


/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
    obtain hc | hc | hc := lt_trichotomy c 0
    rw [tendsTo_def] at *
    intro ε hε
    have hc' : 0 < -c := neg_pos.mpr hc
    have hε_div_c : ε / -c > 0 := div_pos hε hc'
    specialize h (ε / -c) (by linarith)
    cases' h with X hX
    use X
    intro n hn
    specialize hX n hn
    rw [← sub_mul]
    rw [abs_mul]
    rw [mul_comm]
    rw [← abs_neg]
    rw [abs_of_nonneg]
    rw [mul_comm]
    exact (lt_div_iff₀ hc').mp hX
    linarith

    rw [tendsTo_def] at *
    intro ε h2
    use 1
    intro n hn
    rw [hc]
    rw [mul_zero]
    simp
    exact h2

    rw [tendsTo_def] at *
    intro ε hε
    have hε_div_c : ε / c > 0 := div_pos hε hc
    specialize h (ε / c) (by linarith)
    cases' h with X hX
    use X
    intro n hn
    specialize hX n hn
    rw [← sub_mul]
    rw [abs_mul]
    rw [mul_comm]
    rw [abs_of_nonneg]
    rw [mul_comm]
    exact (lt_div_iff₀ hc).mp hX
    linarith





-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize h1 (ε/2) (by linarith)
  specialize h2 (ε/2) (by linarith)
  cases' h1 with X hX
  cases' h2 with Y hY
  use max X Y
  intro n hn
  rw [max_le_iff] at hn
  specialize hX n hn.1
  specialize hY n hn.2
  rw [abs_lt] at *
  constructor <;>
   linarith
  done

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  rw [tendsTo_def]
  constructor
  intro h1
  rw [tendsTo_def]
  intro ε hε
  specialize h1 (ε) (by linarith)
  cases' h1 with X hX
  use X
  intro n hn
  specialize hX n hn
  ring
  exact hX

  rw[tendsTo_def]
  intro h1
  intro ε hε
  specialize h1 (ε) (by linarith)
  cases' h1 with X hX
  use X
  intro n hn
  specialize hX n hn
  rw [abs_lt] at *
  constructor <;>
   linarith

  done






/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize ha ε (by linarith)
  specialize hb 1 (by linarith)
  cases' ha with X hX
  cases' hb with Y hY
  use max X Y
  intro n hn
  rw [max_le_iff] at hn
  specialize hX n hn.1
  specialize hY n hn.2
  rw [sub_zero] at *
  rw [abs_mul]
  have h1: ε*1 = ε := by
    rw [mul_one]
  rw [← h1]
  apply mul_lt_mul'
  linarith
  exact hY
  exact abs_nonneg (b n)
  exact hε


/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
    rw [tendsTo_sub_lim_iff] at *
    have h : ∀ n, a n * b n - t * u = (a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u := by
      intro n
      ring
    rw [tendsTo_def] at *
    intro ε hε
    have hu : (3*(|u| + 1)) > 0 := by linarith [abs_nonneg u]
    have hε_div_u : (ε / (3 * (|u| + 1))) > 0 := div_pos hε hu
    specialize ha (ε / (3 * (|u| + 1))) (by linarith)
    have ht : (3*(|t| + 1)) > 0 := by linarith [abs_nonneg t]
    have hε_div_t : (ε / (3 * (|t| + 1))) > 0 := div_pos hε ht
    specialize hb (ε / (3 * (|t| + 1))) (by linarith)
    cases' ha with X haX
    cases' hb with Y hbY
    use max X Y
    intro n hn
    rw [max_le_iff] at hn
    specialize haX n hn.1
    specialize hbY n hn.2
    rw [sub_zero] at *
    have h1 : |a n * b n - t * u| = |(a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u| := by
     rw [h n]
    have h2 : |(a n - t) * (b n - u)| = |a n - t| * |b n - u| := by
      exact abs_mul (a n - t) (b n - u)
    have h3 : |t * (b n - u)| = |t| * |b n - u| := abs_mul t (b n - u)
    have h4 : |(a n - t) * u| = |a n - t| * |u| := abs_mul (a n - t) u
    have h5 : |(a n - t) * (b n - u)| < (ε / (3 * (|u| + 1))) * (ε / (3 * (|t| + 1))) := by
     rw [abs_mul]
     apply mul_lt_mul''
     exact haX
     exact hbY
     linarith [abs_nonneg (a n - t)]
     linarith [abs_nonneg (b n - u)]
    have h6 : |t * (b n - u)| ≤ |t| * (ε / (3 * (|t| + 1))) := by
     rw [abs_mul]
     apply mul_le_mul_of_nonneg_left
     linarith
     linarith [abs_nonneg t]

    have h7 : |(a n - t) * u| ≤ (ε / (3 * (|u| + 1))) * |u| := by
      rw [abs_mul]
      apply mul_le_mul
      linarith
      linarith
      linarith [abs_nonneg u]
      linarith
    rw [h n]
    have h8 : |(a n - t) * (b n - u) + t * (b n - u)| ≤ |(a n - t) * (b n - u)| + |t * (b n - u)| := by
      apply abs_add_le
    have h9 : |(a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u| ≤ |(a n - t) * (b n - u) + t * (b n - u)| + |(a n - t) * u| := by
      apply abs_add_le
    have h10: |(a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u| ≤ |(a n - t) * (b n - u)| + |t * (b n - u)| + |(a n - t) * u| := by
      linarith [h8, h9]
    have h11: ε / (3 * (|u| + 1)) * (ε / (3 * (|t| + 1))) + |t| * (ε / (3 * (|t| + 1))) + ε / (3 * (|u| + 1)) * |u| < ε := by
      have h11_1 : ε / (3 * (|u| + 1)) * (ε / (3 * (|t| + 1))) = (ε * ε) / ((3 * (|u| + 1)) * (3 * (|t| + 1))) := by
       field_simp [abs_nonneg u, abs_nonneg t]
      have h11_2 : (ε * ε) / ((3 * (|u| + 1)) * (3 * (|t| + 1))) = ε * (ε / (3 * (|u| + 1) * (|t| + 1))) := by
       field_simp [abs_nonneg u, abs_nonneg t]
      have h11_3 : |t| * (ε / (3 * (|t| + 1))) = (|t| * ε) / (3 * (|t| + 1)) := by ring
      have h11_4 : ε / (3 * (|u| + 1)) * |u| = (|u| * ε) / (3 * (|u| + 1)) := by ring
      have h11_5 : (ε * (ε / (3 * (|u| + 1) * (|t| + 1)))) + (|t| * ε) / (3 * (|t| + 1)) + (|u| * ε) / (3 * (|u| + 1)) < ε := by
       field_simp [abs_nonneg u, abs_nonneg t]

      rw [h11_1,h11_2,h11_3,h11_4]
      exact h11_5

    linarith [h5,h6,h7,h10,h11]




-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  by_contra h
  rw [tendsTo_def] at *
