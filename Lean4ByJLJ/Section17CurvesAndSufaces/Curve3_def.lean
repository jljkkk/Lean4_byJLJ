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
  sorry

theorem diff (f : ℝ → ℝ) (x : ℝ) :
  DifferentiableAt ℝ f x ↔ Mydiff f x := by
  sorry

theorem has_der (f : ℝ → ℝ) (f' x  : ℝ) :
  HasDerivAt f f' x ↔ Myhasder f f' x := by
  sorry

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



example (φ : ℝ → ℝ) (ψ : ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hφ : ∀ x, x ∈ Set.Icc a b → φ x ∈ Set.Icc c d)
    (hψ : ∀ y, y ∈ Set.Icc c d → ψ y ∈ Set.Icc a b)
    (left_inv : ∀ x, x ∈ Set.Icc a b → ψ (φ x) = x)
    (right_inv : ∀ y, y ∈ Set.Icc c d → φ (ψ y) = y)
    (hφdiff : ContDiffOn ℝ ⊤ φ (Set.Icc a b))
    (hφregular : ∀ x, x ∈ Set.Icc a b → fderiv ℝ φ x ≠ 0) :
    ContDiffOn ℝ ⊤ ψ (Set.Icc c d) ∧
      ∀ y, y ∈ Set.Icc c d → ∀ z, fderiv ℝ ψ y (fderiv ℝ φ (ψ y) z) = z := by

    have ψ_smooth : ContDiffOn ℝ ⊤ ψ (Icc c d) := by
      rw [contdiffOn_equiv] at *
      intro x hx
      have hy : ψ x ∈ Icc a b := by
        apply hψ at hx
        exact hx
      apply hφdiff at hy
      unfold my_contdiffwithin_at at *
      rw [if_pos] at *
      intro n
      induction n with
      | zero =>
        have aux : my_continuous (my_der_k φ (ψ x) 0 (Icc a b)) (ψ x) (Icc a b) := by
          specialize hy 0
          exact hy

        unfold my_continuous
        unfold my_der_k
        rw [if_pos]
        unfold my_der_k at aux
        rw [if_pos] at aux
        unfold my_continuous at aux
        intro ε hε
        obtain ⟨ δ , δ_pos , hδ ⟩ := aux ε hε
        use δ
        constructor
        exact δ_pos
        intro y hy
        cases' hy with hy1 hy2
        have y_int :  y ∈ Icc c d := by
          cases hy2 with
          | inl hy =>
            exact hy
          | inr hy =>
            rw [mem_singleton_iff] at hy
            rw [hy]
            exact hx

        apply right_inv at hx
        rw [hx] at hδ
        sorry

        simp
        simp



      | succ m' ih =>
        sorry



      simp

      simp

    constructor
    exact ψ_smooth

    intro y hy z
    simp
    rw [mul_assoc]
    have eq_one : deriv φ (ψ y) * deriv ψ y  = 1 := by
      have res : deriv φ (ψ y) = 1 / deriv ψ y := by
        have aux : HasDerivAt ψ (deriv φ (ψ y))⁻¹ y := by
          rw [has_der]
          have der_ne_zero : deriv φ (ψ y) ≠ 0 := by
            apply hψ at hy
            apply hφregular at hy
            rw [← norm_ne_zero_iff] at hy
            rw [← norm_deriv_eq_norm_fderiv] at hy
            rw [Real.norm_eq_abs,abs_ne_zero] at hy
            exact hy

          have hf : HasDerivAt φ (deriv φ (ψ y)) (ψ y) := by
             have aux : DifferentiableAt ℝ φ (ψ y) := by
              apply differentiableAt_of_deriv_ne_zero der_ne_zero
             rw [has_der]
             rw [der_equiv]
             unfold Myderiv
             rw [diff] at aux
             rw [dif_pos]
             exact Classical.choose_spec aux

          rw [has_der] at hf
          unfold Myhasder at *
          let dφ := deriv φ (ψ y)
          intro ε ε_pos
          have dφ_ne_zero : dφ ≠ 0 := der_ne_zero
          let ε' := min (|dφ|/2) (ε * dφ^2 / 2)
          have ε'_pos : 0 < ε' := by
            apply lt_min
            simp
            exact dφ_ne_zero
            positivity

          obtain ⟨δ', δ'_pos, hδ'⟩ := hf ε' ε'_pos
          have ψ_cont : ContinuousAt ψ y := by
            --apply ContDiffOn.continuousOn ψ_smooth y hy
            sorry

          obtain ⟨η, η_pos, hη⟩ : ∃ η > 0, ∀ y₁, |y₁ - y| < η → |ψ y₁ - ψ y| < δ' := by
            sorry

          use min η (ε' * δ' / (|dφ| + ε')), lt_min η_pos (by positivity)
          intro y₁ hy₁
          rcases hy₁ with ⟨y₁_ne, y₁_close⟩
          have y₁_close' : |y₁ - y| < η := (lt_min_iff.mp y₁_close).1
          have y₁_close'' : |y₁ - y| < ε' * δ' / (|dφ| + ε') := (lt_min_iff.mp y₁_close).2
          have hψ_close : |ψ y₁ - ψ y| < δ' := hη y₁ y₁_close'
          by_cases hψ_eq : ψ y₁ = ψ y
          have : y₁ = y := by
            rw [← right_inv y hy, ← right_inv y₁]
            rw [hψ_eq]
            sorry
          rw [this] at y₁_ne
          simp at y₁_ne

          have hdiff : |(φ (ψ y₁) - φ (ψ y)) / (ψ y₁ - ψ y) - dφ| < ε' := by
            apply hδ' (ψ y₁)
            constructor
            simp
            have different : ψ y₁ ≠ ψ y := by
              exact hψ_eq
            rw [← sub_ne_zero] at different
            exact different

            exact hψ_close

          have y₁_eq : y₁ = φ (ψ y₁) := by
            sorry

          have y_eq : y = φ (ψ y) := by
            apply right_inv at hy
            symm
            exact hy

          rw [← y_eq,  ← y₁_eq] at hdiff
          let r := (y₁ - y) / (ψ y₁ - ψ y) - dφ
          have r_bound : |r| < ε' := hdiff
          have dφ_r_ne_zero : dφ + r ≠ 0 := by
            have : |r| < |dφ|/2 := lt_of_lt_of_le r_bound (min_le_left _ _)
            sorry

          have : (ψ y₁ - ψ y) / (y₁ - y) = 1 / (dφ + r) := by
            simp at y₁_ne
            field_simp [sub_ne_zero.mpr y₁_ne, hψ_eq]
            ring
            sorry

          rw [this]
          have : |1 / (dφ + r) - dφ⁻¹| = |r| / |dφ * (dφ + r)| := by
            sorry
          have dφ_eq : dφ = deriv φ (ψ y) := by simp
          rw [← dφ_eq]

          rw [this]

          have d1: |dφ + r| ≥ |dφ| - |r| := by
            sorry
          have d2: |dφ + r| ≥ |dφ| - ε' := by linarith
          have d3: |dφ + r| ≥ |dφ|/2 := by
            have aux : |dφ| - ε' ≥ |dφ|/2 := by
              unfold ε'
              have le_min : |dφ| / 2 ⊓ ε * dφ ^ 2 / 2 ≤  |dφ| / 2 := by
                apply min_le_left
              have sub_le : |dφ| - |dφ|/2 ≥ |dφ|/2 := by
                ring
                simp
              have aux : |dφ| - |dφ| / 2 ⊓ ε * dφ ^ 2 / 2 ≥ |dφ| - |dφ|/2 := by
                apply sub_le_sub_left
                exact le_min

              exact ge_trans aux sub_le

            exact ge_trans d2 aux


          have d4: |dφ * (dφ + r)| ≥ |dφ| * (|dφ|/2) := by
            rw [abs_mul]
            have non_neg : 0 ≤ |dφ| / 2 := by
              apply div_nonneg
              simp
              simp
            apply mul_le_mul le_rfl d3 non_neg (abs_nonneg _)

          have d5: |r| / |dφ * (dφ + r)| ≤ |r| / (|dφ| * (|dφ|/2)) := by
            refine div_le_div_of_nonneg_left (abs_nonneg _) ?_ d4
            positivity

          have d6: |r| / (|dφ| * (|dφ|/2)) = 2 * |r| / |dφ|^2 := by ring
          rw [d6] at *
          have ε'_le : ε' ≤ ε * dφ^2 / 2 := min_le_right _ _

          have d7 : |r| / (|dφ| * (|dφ| / 2)) < ε' / ( dφ ^ 2 / 2) := by
            have: |dφ| * (|dφ| / 2) = dφ ^ 2 / 2 := by
              ring
              simp
            rw [this]
            simp
            rw [div_lt_div_iff_of_pos_right]
            linarith
            apply div_pos
            exact pow_two_pos_of_ne_zero dφ_ne_zero
            simp
          have hpos : dφ ^ 2 / 2 > 0 := by
            apply div_pos
            exact pow_two_pos_of_ne_zero dφ_ne_zero
            simp

          have key : |r| / |dφ * (dφ + r)| < ε' / (dφ^2 / 2) := by
            apply lt_of_lt_of_le' d7 d5
          have ε'_bound : ε' / (dφ^2 / 2) ≤ (ε * dφ^2 / 2) / (dφ^2 / 2) := by
            apply (div_le_div_iff_of_pos_right hpos).mpr ε'_le
          have ε'_simplified : (ε * dφ^2 / 2) / (dφ^2 / 2) = ε := by
            field_simp [hpos.ne']

          rw [ε'_simplified] at ε'_bound
          apply lt_of_le_of_lt' ε'_bound key


          /-
          have hf' : deriv φ (ψ y) ≠ 0 := by
              apply hψ at hy
              apply hφregular at hy
              rw [← norm_ne_zero_iff] at hy
              rw [← norm_deriv_eq_norm_fderiv] at hy
              rw [Real.norm_eq_abs,abs_ne_zero] at hy
              exact hy


          have hfg : ∀ᶠ (y : ℝ) in nhds y, φ (ψ y) = y := by
            rw [Filter.eventually_iff_exists_mem]
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

            /-
            apply ψ_smooth at hy
            rw [cont]
            unfold Mycont
            intro ε hε
            sorry
            -/


          apply HasDerivAt.of_local_left_inverse hg hf hf' hfg
          -/



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
        have hy' : ψ y ∈ Icc a b := by
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
