import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Filter




/-

# Smooth functions

-/

noncomputable def φ₁ : ℝ → ℝ × ℝ := fun x => (Real.cos x, Real.sin x)

-- `ContDiffOn.prod` is a thing etc etc
example : ContDiffOn ℝ ⊤ φ₁ (Set.Icc 0 1) := by
  apply ContDiffOn.prod
  apply ContDiff.contDiffOn
  exact Real.contDiff_cos
  apply ContDiff.contDiffOn
  exact Real.contDiff_sin



open Real
open Set

noncomputable def φ₂ : ℝ → ℝ × ℝ × ℝ := fun x => (Real.sin x, x ^ 4 + 37 * x ^ 2 + 1, abs x)

example : ContDiffOn ℝ ⊤ φ₂ (Set.Icc 0 1) := by
  apply ContDiffOn.prod
  apply ContDiff.contDiffOn
  exact Real.contDiff_sin
  apply ContDiffOn.prod
  apply ContDiff.contDiffOn
  apply ContDiff.add
  apply ContDiff.add
  apply ContDiff.pow
  apply contDiff_id
  apply ContDiff.mul
  apply contDiff_const
  apply ContDiff.pow
  apply contDiff_id
  apply contDiff_const
  apply contDiffOn_id.congr
  simp
  intro h h1 h2
  exact h1





-- AFAIK nobody did the below example yet (including me)
/- Let `a≤b` and `c≤d` be reals. Let φ : [a,b] → [c,d] and ψ : [c,d] → [a,b]
  be inverse bijections, and assume φ is smooth and φ' is nonvanishing
  on [a,b]. Then ψ is smooth and ψ' is nonvanishing on [c,d],
  and ψ'(y)*φ'(ψ(y))=1.
-/
def Myhasder  (f : ℝ → ℝ) (f' x  : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, 0 < |y - x| ∧ |y - x| < δ   → |(f (y) - f x) / (y-x) - f'| < ε

def Mydiff (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ (f' : ℝ ), Myhasder f f' x

def Mycont (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ   →  |f y - f x| < ε

open Classical in
noncomputable def Myderiv (f : ℝ → ℝ) (x: ℝ) : ℝ  :=
  if h: Mydiff f x  then
    Classical.choose h
  else
    0

theorem cont (f : ℝ → ℝ) (x : ℝ):
  ContinuousAt f x ↔ Mycont f x := by
  constructor
  intro h
  unfold Mycont
  rw [Metric.continuousAt_iff] at h
  intro ε hε
  obtain ⟨ δ, δ_pos, hδ ⟩ := h ε hε
  use δ
  constructor
  exact δ_pos
  intro y hy
  apply hδ at hy
  rw [Real.dist_eq] at hy
  exact hy

  intro h
  rw [Metric.continuousAt_iff]
  unfold Mycont at h
  intro ε hε
  obtain ⟨ δ, δ_pos, hδ ⟩ := h ε hε
  use δ
  constructor
  exact δ_pos
  intro y hy
  apply hδ at hy
  rw [Real.dist_eq]
  exact hy

theorem has_der (f : ℝ → ℝ) (f' x  : ℝ) :
  HasDerivAt f f' x ↔ Myhasder f f' x := by
  constructor
  intro h
  unfold Myhasder
  rw [hasDerivAt_iff_tendsto] at h
  intro ε hε
  rcases (Metric.tendsto_nhds_nhds.1 h) ε hε with ⟨δ, hδ_pos, hδ⟩
  use δ

  constructor
  exact hδ_pos

  intro y hy
  cases' hy with hy1 hy2
  apply hδ at hy2
  rw [Real.dist_eq] at hy2
  simp at hy2
  rw [← abs_inv] at hy2
  rw [← abs_mul] at hy2
  rw [abs_abs,inv_mul_eq_div, sub_div, mul_comm,← mul_div,div_self, mul_one] at hy2
  exact hy2
  rw [← abs_ne_zero]
  rw [← abs_pos]
  rw [abs_abs]
  exact hy1

  intro h
  rw [hasDerivAt_iff_tendsto]
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  obtain ⟨ δ , δ_pos, hδ  ⟩ := h ε hε
  use δ
  constructor
  exact δ_pos
  intro z hz
  rw [Real.dist_eq]
  simp
  rw [← abs_inv,← abs_mul,abs_abs,inv_mul_eq_div, sub_div, mul_comm,← mul_div]
  by_cases hxz_eq : z = x
  rw [hxz_eq]
  simp
  exact hε
  have hxz_des : z - x ≠ 0 := by
    rw [sub_ne_zero]
    exact hxz_eq

  rw [← abs_ne_zero] at hxz_des
  rw [← abs_pos] at hxz_des
  rw [abs_abs] at hxz_des
  specialize hδ z
  have aux: 0 < |z - x| ∧ |z - x| < δ  := by
    constructor
    exact hxz_des
    rw [Real.dist_eq] at hz
    exact hz

  apply hδ at aux
  rw [div_self, mul_one]
  exact aux
  rw [← abs_ne_zero]
  linarith


theorem diff (f : ℝ → ℝ) (x : ℝ) :
  DifferentiableAt ℝ f x ↔ Mydiff f x := by
  constructor
  intro h
  rw [DifferentiableAt] at h
  unfold Mydiff
  obtain ⟨ f', hf' ⟩ := h
  use (f' 1)
  rw [← has_der]
  rw [hasFDerivAt_iff_hasDerivAt] at hf'
  exact hf'

  intro h
  rw [Mydiff] at h
  rw [DifferentiableAt]
  obtain ⟨ f', hf⟩  := h
  rw [← has_der] at hf
  rw [hasDerivAt_iff_hasFDerivAt] at hf
  let g : ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) f'
  use g
  exact hf

theorem der_unique (f : ℝ → ℝ) ( f1' f2' x : ℝ) (h0: Myhasder f f1' x) (h1: Myhasder f f2' x):
  f1' = f2'  := by
  sorry

theorem der_equiv (f : ℝ → ℝ) (x  : ℝ) :
  deriv f x = Myderiv f x := by
  sorry


def my_has_der (f f': ℝ → ℝ) (x  : ℝ) (s : Set ℝ ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, 0 < |y - x| ∧ |y - x| < δ ∧ y ∈ s ∪ {x}  → |(f (y) - f x) / (y-x) - f' x| < ε

def my_diff (f : ℝ → ℝ) (x : ℝ) (s : Set ℝ ) : Prop :=
  ∃ (f' : ℝ → ℝ), my_has_der f f' x s


open Classical in
noncomputable def my_deriv (f : ℝ → ℝ) (x: ℝ) (s : Set ℝ) : ℝ → ℝ :=
  if h: my_diff f x s then
    Classical.choose h
  else
    fun _ => 0


def my_continuous (f : ℝ → ℝ) (x : ℝ) (s : Set ℝ ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ ∧ y ∈ s ∪ {x}  →  |f y - f x| < ε

noncomputable def my_der_k (f : ℝ → ℝ) (x : ℝ) (k : ℕ) (s: Set ℝ ) : ℝ → ℝ :=
  if k = 0 then
    f
  else
    my_deriv (my_der_k f x (k - 1) s) x s


def my_contdiffwithin_at (f : ℝ → ℝ) (x : ℝ) (n : WithTop ℕ∞) (s : Set ℝ) : Prop :=
  if n = ⊤ then
    ∀ n : ℕ, my_continuous (my_der_k f x n s) x s
  else
    ∃ n' : ℕ, ↑n' = n ∧
    ∀ k ≤ n', my_continuous (my_der_k f x k s) x s


theorem cont_der_k (f : ℝ → ℝ) (x : ℝ)  (s : Set ℝ) :
  (∀ (n : ℕ), my_continuous (my_der_k f x n s) x s) ↔ (∀ (n : ℕ), ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ ∧ y ∈ s ∪ {x}  → |(my_der_k f x n s) (y) - (my_der_k f x n s) x| < ε) := by
  constructor
  intro h n
  specialize h n
  rw [my_continuous] at h
  exact h
  intro h n
  specialize h n
  rw [my_continuous]
  exact h

theorem my_has_der_equiv (f f': ℝ → ℝ) (x  : ℝ) ( s : Set ℝ) :
  HasDerivWithinAt f (f' x) s x ↔ my_has_der f f' x s := by
  constructor
  intro h
  rw [my_has_der]
  rw [hasDerivWithinAt_iff_tendsto] at h

  intro ε hε
  rcases (Metric.tendsto_nhdsWithin_nhds.1 h) ε hε with ⟨δ, hδ_pos, hδ⟩
  use δ

  constructor
  exact hδ_pos

  intro y hy
  cases' hy with hy1 hy2
  cases' hy2 with hy1_eq hy1_not
  apply hδ at hy1_eq
  rw [Real.dist_eq] at hy1_eq
  simp at hy1_eq
  rw [← abs_inv] at hy1_eq
  rw [← abs_mul] at hy1_eq
  rw [abs_abs,inv_mul_eq_div, sub_div, mul_comm,← mul_div,div_self, mul_one] at hy1_eq
  exact hy1_eq

  rw [← abs_ne_zero]
  linarith
  rcases hy1_not with hy11 | hy12
  exact hy11
  exfalso
  have h_y_eq_x : y = x := mem_singleton_iff.1 hy12
  rw [h_y_eq_x] at hy1
  simp at hy1

  intro h
  rw [hasDerivWithinAt_iff_tendsto]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [my_has_der] at h
  obtain ⟨ δ , δ_pos, hδ  ⟩ := h ε hε
  use δ
  constructor
  exact δ_pos
  intro z hz
  rw [Real.dist_eq]
  intro h_xz
  rw [Real.dist_eq]
  simp
  rw [← abs_inv,← abs_mul,abs_abs,inv_mul_eq_div, sub_div, mul_comm,← mul_div]
  by_cases hxz_eq : z = x
  rw [hxz_eq]
  simp
  exact hε
  have hxz_des : z - x ≠ 0 := by
    rw [sub_ne_zero]
    exact hxz_eq

  rw [← abs_ne_zero] at hxz_des
  rw [← abs_pos] at hxz_des
  rw [abs_abs] at hxz_des
  specialize hδ z
  have aux: 0 < |z - x| ∧ |z - x| < δ ∧ z ∈ s ∪ {x} := by
    constructor
    exact hxz_des
    constructor
    exact h_xz
    left
    exact hz

  apply hδ at aux
  rw [div_self, mul_one]
  exact aux
  rw [← abs_ne_zero]
  linarith


theorem my_diff_equiv (f : ℝ → ℝ) (x : ℝ) ( s : Set ℝ):
  DifferentiableWithinAt ℝ f s x ↔ my_diff f x s:= by
  constructor
  rw [DifferentiableWithinAt]
  intro h
  rw [my_diff]
  obtain ⟨ f', hf⟩  := h
  use λ x => (f' 1)
  rw [← my_has_der_equiv]
  rw [hasFDerivWithinAt_iff_hasDerivWithinAt] at hf
  exact hf

  intro h
  rw [my_diff] at h
  rw [DifferentiableWithinAt]
  obtain ⟨ f', hf⟩  := h
  rw [← my_has_der_equiv] at hf
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at hf
  let g : ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (f' x)
  use g
  exact hf

lemma my_has_der_unique (f f₁' f₂' : ℝ → ℝ) (x : ℝ) (s : Set ℝ)
  (h1 : my_has_der f f₁' x s) (h2 : my_has_der f f₂' x s) :
  f₁' x = f₂' x := by
  by_contra h
  rw [← ne_eq] at h
  have aux :  f₁' x - f₂' x ≠ 0 := by
    simp
    rw [sub_eq_zero]
    exact h

  rw [← abs_pos] at aux
  let ε := |f₁' x - f₂' x| / 2
  have εpos : ε > 0 := by
    unfold ε
    linarith

  have h1x := h1 ε εpos
  have h2x := h2 ε εpos
  obtain ⟨ δ1 , δ1_pos, hδ1 ⟩ := h1x
  obtain ⟨ δ2 , δ2_pos, hδ2 ⟩ := h2x
  let δ := min δ1 δ2
  sorry

theorem my_deriv_equiv (f : ℝ → ℝ) (x: ℝ) ( s : Set ℝ):
  derivWithin f s x = my_deriv f x s x := by
  rw [derivWithin]
  rw [fderivWithin]
  let zero : ℝ →L[ℝ] ℝ := 0
  let zero' : ℝ → ℝ := λ x => (zero 1)
  have aux : HasFDerivWithinAt f zero s x ↔ my_has_der f zero' x s := by
    rw [← my_has_der_equiv]
    rw [hasFDerivWithinAt_iff_hasDerivWithinAt]

  by_cases h_zero : HasFDerivWithinAt f zero s x

  rw [if_pos]
  rw [aux] at h_zero
  simp
  have res : my_deriv f x s x = 0:= by
    have h_diff : my_diff f x s := by
      rw [my_diff]
      use zero'

    have deriv_eq : my_deriv f x s x = zero' x := by
      apply my_has_der_unique f (my_deriv f x s) zero' x s _ h_zero
      unfold my_deriv
      simp [h_diff]
      exact Classical.choose_spec h_diff

    rw [deriv_eq]
    unfold zero'
    unfold zero
    simp


  rw [eq_comm]
  exact res
  exact h_zero

  sorry


theorem my_continuous_equiv (f : ℝ → ℝ) (x : ℝ) ( s : Set ℝ) :
  ContinuousWithinAt f s x ↔ my_continuous f x s := by
  rw [Metric.continuousWithinAt_iff]
  rw [my_continuous]
  constructor
  intro h
  intro ε hε
  obtain ⟨ δ , δ_pos , hδ ⟩ := h ε hε
  use δ
  constructor
  exact δ_pos
  intro y hy
  cases' hy with hy1 hy2
  cases' hy2 with hy21 hy22
  apply hδ at hy21
  rw [Real.dist_eq] at hy21
  apply hy21 at hy1
  rw [Real.dist_eq] at hy1
  exact hy1
  have aux : y = x := mem_singleton_iff.1 hy22
  rw [aux]
  simp
  exact hε

  intro h
  intro ε hε
  obtain ⟨ δ , δ_pos , hδ ⟩ := h ε hε
  use δ
  constructor
  exact δ_pos
  intro z hz hz_dist
  rw [Real.dist_eq] at *
  have hz : z ∈ s ∪ {x} := by
    left
    exact hz

  have aux : |z - x| < δ ∧ z ∈ s ∪ {x} := by
    constructor
    exact hz_dist
    exact hz

  apply hδ at aux
  exact aux


theorem my_taylor (f : ℝ → ℝ) (x : ℝ) (k : ℕ) (s : Set ℝ) (p : ℝ → FormalMultilinearSeries ℝ ℝ ℝ) (u : Set ℝ)
 (hp : HasFTaylorSeriesUpToOn (↑k) f p u) (hu : u ∈ nhdsWithin x (insert x s)):
   my_der_k f x k s = (fun (x : ℝ ) => (p x k) (λ _ => 1)) := by
  sorry -- This is a placeholder for the actual proof, which would involve showing the equivalence of the definitions.

theorem taylor_cont (f : ℝ → ℝ) (x : ℝ) (k : ℕ) (s : Set ℝ) (p : ℝ → FormalMultilinearSeries ℝ ℝ ℝ) (u : Set ℝ)
 (hp : HasFTaylorSeriesUpToOn (↑k) f p u) (hu : u ∈ nhdsWithin x (insert x s)) :
  ContinuousWithinAt (fun (x : ℝ ) => (p x k) (λ _ => 1)) s x := by
  sorry -- This is a placeholder for the actual proof, which would involve showing the equivalence of the definitions.

theorem my_eq_abs (f : ℝ → ℝ) (x y z: ℝ) :
  |f z - f y  + f x - f x| = |f z - f y| := by
  sorry

theorem my_des_abs (f : ℝ → ℝ) (x y z: ℝ) :
  |f z - f y + f x - f x| <= |f x - f z| + |f x - f y|  := by
  sorry

theorem contdiffOn_equiv (f : ℝ → ℝ) (n : WithTop ℕ∞) ( s : Set ℝ) :
   ContDiffOn ℝ n f s  ↔  (∀ x ∈ s, my_contdiffwithin_at f x n s) := by

  constructor --La prueba de =>
  intro h x hx
  rw [my_contdiffwithin_at]
  rw [ContDiffOn] at h
  apply h at hx
  split_ifs with hn --Distincion de casos sobre si n = T o no
  --Caso n = T
  intro k
  have contdiff_k : ContDiffWithinAt ℝ k f s x := by
    have hk : k ≤ n := by
      rw [hn]
      simp
    apply ContDiffWithinAt.of_le hx hk

  rw [ContDiffWithinAt.eq_def] at contdiff_k
  specialize contdiff_k k (le_rfl)
  obtain ⟨u, hu, p, hp⟩ := contdiff_k
  have h_der_eq : my_der_k f x k s = (fun (x : ℝ ) => (p x k) (λ _ => 1))   := by
    exact my_taylor f x k s p u hp hu

  rw [h_der_eq]
  rw [← my_continuous_equiv]
  exact taylor_cont f x k s p u hp hu
  --Caso n ≠ T
  have hne : n ≠ ⊤ := hn
  rw [WithTop.ne_top_iff_exists] at hne
  obtain ⟨n1, hn1⟩ := hne
  have hmn : ∃ n' : ℕ, ↑n' = n := by
    sorry
  obtain ⟨m, hm⟩ := hmn
  use m
  constructor
  exact hm

  intro k hk
  have contdiff_k : ContDiffWithinAt ℝ k f s x := by
    have hk : ↑k ≤ n := by
      rw [←hm]
      simp
      exact hk
    apply ContDiffWithinAt.of_le hx hk

  rw [ContDiffWithinAt.eq_def] at contdiff_k
  specialize contdiff_k k (le_rfl)
  obtain ⟨u, hu, p, hp⟩ := contdiff_k
  have h_der_eq : my_der_k f x k s = (fun (x : ℝ ) => (p x k) (λ _ => 1))   := by
    exact my_taylor f x k s p u hp hu

  rw [h_der_eq]
  rw [← my_continuous_equiv]
  exact taylor_cont f x k s p u hp hu

  --Prueba de <=

  intro h
  rw [ContDiffOn]
  intro x hx
  have hx' : x ∈ s := by exact hx
  apply h at hx
  rw [my_contdiffwithin_at] at hx
  cases' n with n1 n2 --Distincion de casos sobre n = T o no
  rw [if_pos rfl] at hx --Caso n = T
  rw [cont_der_k] at hx
  rw [contDiffWithinAt_omega_iff_analyticWithinAt]
  rw [AnalyticWithinAt]
  let a : ℕ → ℝ := fun n => (my_der_k f x n s x) / (Nat.factorial n)
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (a n)

  use p
  rw [HasFPowerSeriesWithinAt]
  let δ_n : Set ℝ := {δ : ℝ | ∀ (n : ℕ), ∀ ε > 0 ,∀ (h : ℝ), |h| < δ ∧ h ∈ s ∪ {x} → |my_der_k f x n s (x + h) - my_der_k f x n s x| < ε}
  let r : ℝ := sInf δ_n
  use ENNReal.ofReal r
  constructor

  sorry

  simp
  sorry
  sorry


  --Caso n ≠ T
  rw [contDiffWithinAt_iff_forall_nat_le]
  intro m hm
  rw [if_neg] at hx
  obtain ⟨n', hn'⟩ := hx
  cases' hn' with h1 h2
  induction m with --Prueba por inducción sobre ℕ
  | zero => --Caso base

    simp
    rw [contDiffWithinAt_zero]
    have h_cont_zero : my_continuous (my_der_k f x 0 s) x s := by
      refine h2 0 ?_
      simp

    rw [my_continuous] at h_cont_zero
    obtain ⟨δ , δ_pos, hδ⟩ := h_cont_zero 1  (by norm_num)
    use Ioo (x - δ) (x + δ)
    constructor

    have h_inf :  x - δ < x := by
      apply sub_lt_self
      exact δ_pos
    have h_sup : x + δ > x := by
      apply lt_add_of_pos_right
      exact δ_pos
    apply mem_nhdsWithin_of_mem_nhds
    exact Ioo_mem_nhds h_inf h_sup

    intro y hy
    rw [my_der_k] at h_cont_zero
    rw [if_pos rfl] at h_cont_zero
    rw [continuousWithinAt_inter]

    by_cases h_eq : y = x
    rw [h_eq]
    rw [← my_continuous] at h_cont_zero
    rw [← my_continuous_equiv] at h_cont_zero
    exact h_cont_zero

    rw [my_continuous_equiv]
    rw [my_continuous]
    intros ε ε_pos
    have hε : 0 < ε/2 := by
      linarith
    obtain ⟨δ₁, δ₁_pos, H⟩ := h_cont_zero (ε/2) hε
    set δ' := min (min δ₁ |y - x + δ|/2)  |x + δ - y|/2  with hδ'
    have hδ'_pos : 0 < δ' := by
      rw [hδ']
      simp

      have aux : y ∈ Ioo (x - δ) (x + δ) := by
        exact hy.2
      simp at aux
      constructor
      constructor
      exact δ₁_pos


      have aux1 : y - x + δ ≠ 0 := by
        linarith

      exact aux1

      have aux2 : x + δ - y ≠ 0 := by
        linarith

      exact aux2


    use δ'
    constructor
    exact hδ'_pos
    intros z h1
    rw [← my_eq_abs f x y z]
    have des_abs : |f z - f y + f x - f x| <= |f x - f z| + |f x - f y| := by
      apply my_des_abs

    have des1 : |f x - f z| < ε/2 := by
      have interior: |z - x| < δ₁ ∧ z ∈ s ∪ {x} := by
        sorry
      apply H at interior
      rw [abs_sub_comm]
      exact interior

    have des2 : |f x - f y| < ε/2 := by
      have interior: |y - x| < δ₁ ∧ y ∈ s ∪ {x} := by
        sorry
      apply H at interior
      rw [abs_sub_comm]
      exact interior

    linarith
    rw [mem_nhds_iff]
    use Ioo (x - δ) (x + δ)
    constructor
    exact subset_rfl
    constructor
    exact isOpen_Ioo
    exact hy.2

    exact hx'




  | succ m' ih => --Paso inductivo
    -- Prove for m'+1 using the inductive hypothesis for m'
    let k : WithTop ℕ∞  := ↑(m' + 1)
    have aux : k = ↑(m') + 1 := by rfl
    unfold k at aux
    rw [aux]
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt]

    sorry
    simp

  simp



example (φ : ℝ → ℝ) (ψ : ℝ → ℝ) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hφ : ∀ x, x ∈ Set.Ioo a b → φ x ∈ Set.Ioo c d)
    (hψ : ∀ y, y ∈ Set.Ioo c d → ψ y ∈ Set.Ioo a b)
    (left_inv : ∀ x, x ∈ Set.Ioo a b → ψ (φ x) = x)
    (right_inv : ∀ y, y ∈ Set.Ioo c d → φ (ψ y) = y)
    (hφdiff : ContDiffOn ℝ ⊤ φ (Set.Ioo a b))
    (hφregular : ∀ x, x ∈ Set.Ioo a b → fderiv ℝ φ x ≠ 0) :
    ContDiffOn ℝ ⊤ ψ (Set.Ioo c d) ∧
      ∀ y, y ∈ Set.Ioo c d → ∀ z, fderiv ℝ ψ y (fderiv ℝ φ (ψ y) z) = z := by

      constructor

      sorry

      intro y hy z
      simp
      rw [mul_assoc]
      have eq_one : deriv φ (ψ y) * deriv ψ y  = 1 := by
        have res : deriv φ (ψ y) = 1 / deriv ψ y := by
          have aux : HasDerivAt ψ (deriv φ (ψ y))⁻¹ y := by
            have hf' : deriv φ (ψ y) ≠ 0 := by
              apply hψ at hy
              apply hφregular at hy
              rw [← norm_ne_zero_iff] at hy
              rw [← norm_deriv_eq_norm_fderiv] at hy
              rw [Real.norm_eq_abs,abs_ne_zero] at hy
              exact hy


            have hfg : ∀ᶠ (y : ℝ) in nhds y, φ (ψ y) = y := by
              rw [Filter.eventually_iff_exists_mem]
              let ε : ℝ := min ((y - c)/2) ((d - y)/2)
              use Ioo (y - ε ) (y + ε )
              constructor
              rw [mem_nhds_iff]
              use Ioo (y - ε ) (y + ε )
              constructor
              exact subset_rfl
              constructor
              exact isOpen_Ioo
              simp only [mem_Ioo]
              have ε_pos : ε > 0 := by
                unfold ε
                apply lt_min
                linarith [hy.1]
                linarith [hy.2]
              exact ⟨sub_lt_self y (by positivity), lt_add_of_pos_right y (by positivity)⟩
              intro z hz
              apply right_inv
              rcases hz with ⟨hz_left, hz_right⟩
              rcases hy with ⟨hy_left, hy_right⟩
              have le_left : ε <= (y - c)/2 := by
                unfold ε
                apply min_le_left
              have le_right : ε <= (d - y)/2 := by
                unfold ε
                apply min_le_right
              constructor
              sorry
              sorry

            have hf : HasDerivAt φ (deriv φ (ψ y)) (ψ y) := by
              have aux : DifferentiableAt ℝ φ (ψ y) := by
                apply differentiableAt_of_deriv_ne_zero hf'
              rw [has_der]
              rw [der_equiv]
              unfold Myderiv
              rw [diff] at aux
              rw [dif_pos]
              exact Classical.choose_spec aux

            have aux: DifferentiableAt ℝ ψ y := by
              have ne_zero : deriv ψ y ≠ 0 := by
                intro h
                sorry

              apply differentiableAt_of_deriv_ne_zero ne_zero

            have hg : ContinuousAt ψ y := by
              apply DifferentiableAt.continuousAt aux

            apply HasDerivAt.of_local_left_inverse hg hf hf' hfg

          nth_rewrite 2 [der_equiv]
          unfold Myderiv
          rw [has_der] at aux
          rw [dif_pos]
          have unique_der : @Classical.choose ℝ (fun x ↦ Myhasder ψ x y) ?hc = (deriv φ (ψ y))⁻¹ := by
            apply der_unique ψ
            have h_ex : ∃ f', Myhasder ψ f' y := by
              use (deriv φ (ψ y))⁻¹
            exact Classical.choose_spec h_ex
            exact aux

          rw[unique_der]
          simp
          rw [Mydiff]
          use (deriv φ (ψ y))⁻¹

        rw [res]
        let k : ℝ := deriv ψ y
        have aux:  k = deriv ψ y := by
          unfold k
          rfl
        have h_ne : k ≠ 0 := by
          have hy' : ψ y ∈ Ioo a b := by
            apply hψ at hy
            exact hy
          apply hφregular at hy'
          rw [← norm_ne_zero_iff] at hy'
          rw [← norm_deriv_eq_norm_fderiv] at hy'
          rw [Real.norm_eq_abs] at hy'
          rw [abs_ne_zero] at hy'
          rw [res] at hy'
          intro h
          simp at hy'
          apply hy'
          exact h

        rw [mul_comm,← aux,mul_one_div_cancel]
        exact h_ne


      rw [eq_one]
      simp
