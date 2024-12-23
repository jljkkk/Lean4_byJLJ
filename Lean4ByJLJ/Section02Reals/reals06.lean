import Mathlib.Tactic -- imports all the Lean tactics
import Lean4ByJLJ.Section02Reals.reals05


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





-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  have h : TendsTo (fun n ↦ a n - a n) (s - t) := by
    rw [tendsTo_def] at *
    intro ε hε
    specialize ht (ε / 2) (by linarith)
    cases' ht with X hX
    obtain ⟨Y, hY⟩ := hs (ε / 2) (by linarith)
    use max X Y
    intro n hn
    specialize hX n (le_of_max_le_left hn)
    specialize hY n (le_of_max_le_right hn)
    rw [abs_lt] at *
    constructor <;>
      linarith

  rw [tendsTo_def] at *
  by_contra hcontra
  have h' : s ≠ t := hcontra
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ε ≤ |s - t| := by
    have hd : |s-t| > 0 := by
      by_contra hd1
      simp at hd1
      apply h'
      linarith
    use |s-t|/2
    constructor
    linarith
    linarith
  have hε' : ε > 0 := hε.left
  specialize h ε (by linarith)
  cases' h with X hX
  simp at hX
  have hX' : X ≤ X := by linarith
  specialize hX X hX'
  have hε'' : ε ≤ |s - t| := hε.right
  rw [abs_sub_comm] at hX
  linarith [hε'', hX]
