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
  specialize h (ε / c) (by linarith)
  cases' h with X hX
  use X
  intro n hn
  specialize hX n hn
  rw [← mul_sub]
  rw [abs_mul]
  rw [abs_of_nonneg]


/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize h (ε / -c) (by linarith)
  use 1
  intro n hn
  cases' h with X hX
  specialize hX n hn
  rw [← mul_sub]
  rw [abs_mul]
  rw [← abs_neg]
  rw [abs_of_nonneg]





/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    rw [tendsTo_def] at *
    intro ε hε
    specialize h (ε / |c|) (by linarith)
    cases' h with X hX
    use X
    intro n hn
    specialize hX n hn
    rw [← mul_sub]
    rw [abs_mul]



/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
    rw [tendsTo_def] at *
    intro ε hε
    specialize h (ε / |c|) (by linarith)
    cases' h with X hX
    use X
    intro n hn
    specialize hX n hn
    rw [← sub_mul]
    rw [abs_mul]
    rw [mul_comm]

/-- mismo problema que el anterior, no se si se podria dividir en lean-/

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  rw [tendsTo_def] at *
  intro ε hε
  use 1
  intro n hn
  specialize h1 (ε/2) (by linarith)
  specialize h2 (ε/2) (by linarith)
  cases' h1 with X hX
  cases' h2 with Y hY
  specialize hX n hn
  specialize hY n hn
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
  use 1
  intro n hn
  specialize h1 (ε) (by linarith)
  cases' h1 with X hX
  specialize hX n hn
  ring
  exact hX
  rw[tendsTo_def]
  intro h1
  intro ε hε
  use 1
  intro n hn
  specialize h1 (ε) (by linarith)
  cases' h1 with X hX
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
  use 1
  intro n hn
  specialize ha (ε^(1/2)) (by linarith)
  specialize hb (ε^(1/2)) (by linarith)
  cases' ha with X hX
  cases' hb with Y hY
  specialize hX n hn
  specialize hY n hn


/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  rw [tendsTo_def] at *




-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  rw [tendsTo_def] at *
