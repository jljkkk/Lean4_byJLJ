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



example (φ : ℝ → ℝ) (ψ : ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hφ : ∀ x, x ∈ Set.Ioo a b → φ x ∈ Set.Ioo c d)
    (hψ : ∀ y, y ∈ Set.Ioo c d → ψ y ∈ Set.Ioo a b)
    (left_inv : ∀ x, x ∈ Set.Ioo a b → ψ (φ x) = x)
    (right_inv : ∀ y, y ∈ Set.Ioo c d → φ (ψ y) = y)
    (hφdiff : ContDiffOn ℝ ⊤ φ (Set.Ioo a b))
    (hφregular : ∀ x, x ∈ Set.Ioo a b → fderiv ℝ φ x ≠ 0) :
    ContDiffOn ℝ ⊤ ψ (Set.Ioo c d) ∧
      ∀ y, y ∈ Set.Ioo c d → ∀ z, fderiv ℝ ψ y (fderiv ℝ φ (ψ y) z) = z := by


    have ψ_smooth : ContDiffOn ℝ ⊤ ψ (Ioo c d) := by
        intro y hy
        have hx : ψ y ∈ Ioo a b := hψ y hy
        have hφ_smooth_at : ContDiffAt ℝ ⊤ φ (ψ y) := by
          cases' hx with ha hb
          /-Case (a,b)-/
          have h: Ioo a b ∈ nhds (ψ y) := by
            rw [mem_nhds_iff]
            use Ioo a b
            constructor
            exact subset_refl (Ioo a b)
            constructor
            exact isOpen_Ioo
            simp
            constructor
            exact ha
            exact hb
          exact hφdiff.contDiffAt h

        set x := ψ y with hx_def
        have hx_mem : x ∈ Ioo a b := hx

        have hx_fder_nonzero : fderiv ℝ φ x ≠ 0 := by
          apply hφregular
          exact hx_mem

        have hφ_deriv_ne_zero: deriv φ x ≠ 0 := by
          rw [←fderiv_deriv]
          intro h1
          apply hx_fder_nonzero
          ext t
          rw [h1]
          simp

        have hdiff : DifferentiableAt ℝ φ x := by
          apply differentiableAt_of_deriv_ne_zero
          exact hφ_deriv_ne_zero

        have hφ_strict_deriv : HasStrictDerivAt φ (deriv φ x) x := by
          apply ContDiffAt.hasStrictDerivAt hφ_smooth_at
          simp

        let φ' : ℝ ≃L[ℝ] ℝ :=
          ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv φ x : ℝ) hφ_deriv_ne_zero)

        have hf' : HasFDerivAt φ (φ' : ℝ →L[ℝ] ℝ) x := by
          rw [HasFDerivAt]
          convert hφ_strict_deriv.hasFDerivAt

        have : ContDiffAt ℝ ⊤ φ x := hφ_smooth_at

        have hn: 1 ≤ (⊤ : WithTop ℕ∞)  := by simp

        have inv_theorem := hφ_smooth_at.to_localInverse hf' (by simp)

        have hφ_smooth_at_inv : ContDiffAt ℝ ⊤ (hφ_smooth_at.localInverse hf' (by simp))  (φ x) := by
          apply ContDiffAt.to_localInverse

        have φx_eq_y : φ x = y := by rw [←right_inv y hy, hx_def]

        have local_inv: ψ =ᶠ[nhds (φ x)] (hφ_smooth_at.localInverse hf' (by simp)) := by

          apply Filter.eventuallyEq_of_left_inv_of_right_inv
          have left_inv_eventually : ∀ᶠ z in nhds x, ψ (φ z) = z := by
            rw [eventually_nhds_iff]
            use Ioo a b
            constructor
            intro y hy
            apply left_inv
            exact hy
            constructor
            apply isOpen_Ioo
            exact hx
          exact left_inv_eventually

          apply HasStrictFDerivAt.eventually_right_inverse

          rw [Filter.tendsto_def]
          have inv_continuous: ContinuousAt (hφ_smooth_at.localInverse hf' (by simp)) (φ x) := by
            apply ContDiffAt.continuousAt at hφ_smooth_at_inv
            exact hφ_smooth_at_inv

          intro s hs

          have id_x : (hφ_smooth_at.localInverse hf' (by simp)) (φ x) = x := by
            apply ContDiffAt.localInverse_apply_image

          rw [← id_x] at hs

          apply ContinuousAt.preimage_mem_nhds

          exact inv_continuous
          exact hs


        have : ContDiffAt ℝ ⊤ ψ y := by
          rw [←φx_eq_y]
          apply ContDiffAt.congr_of_eventuallyEq
          apply inv_theorem
          exact local_inv


        have : ContDiffWithinAt ℝ ⊤ ψ (Ioo c d) y := by
          exact this.contDiffWithinAt

        exact this

    have hψ_diff : ∀ y ∈ Ioo c d, DifferentiableAt ℝ ψ y := by
        have aux: DifferentiableOn ℝ ψ (Ioo c d) := by
          apply ψ_smooth.differentiableOn
          simp
        intro y hy
        apply aux.differentiableAt
        rw [mem_nhds_iff]
        use Ioo c d
        constructor
        exact subset_refl (Ioo c d)
        constructor
        exact isOpen_Ioo
        exact hy

    have hφ_diff : ∀ y ∈ Ioo c d, DifferentiableAt ℝ φ (ψ y) := by
      intro y hy
      apply differentiableAt_of_deriv_ne_zero
      have hx_fder_nonzero : fderiv ℝ φ (ψ y) ≠ 0 := by
        apply hφregular
        apply hψ y hy
      rw [←fderiv_deriv]
      intro h1
      apply hx_fder_nonzero
      ext t
      rw [h1]
      simp

    constructor

    exact ψ_smooth

    intro y hy z

    simp

    have h_id : ∀ y ∈ Ioo c d, φ (ψ y) = id y := by
        intro y hy
        apply right_inv
        exact hy
    have h_id_deriv : ∀ y ∈ Ioo c d, deriv (φ ∘ ψ) y = deriv id y := by
      intro y hy
      apply Filter.EventuallyEq.deriv_eq

      apply Filter.eventuallyEq_of_left_inv_of_right_inv

      rw [eventually_nhds_iff]
      use Ioo c d
      constructor
      intro y hy
      apply right_inv
      exact hy
      constructor
      apply isOpen_Ioo
      exact hy

      rw [eventually_nhds_iff]
      use Ioo c d
      constructor
      intro y hy
      simp
      constructor
      apply isOpen_Ioo
      exact hy

      rw [Filter.tendsto_def]
      have inv_continuous: ContinuousAt id y := by
        apply continuousAt_id

      intro s hs
      exact hs

    have chain_deriv : ∀ y ∈ Ioo c d, deriv (φ ∘ ψ) y = (deriv φ (ψ y)) * (deriv ψ y) := by
      intro y hy
      have hφ_diff_at : DifferentiableAt ℝ φ (ψ y) := hφ_diff y hy
      have hψ_diff_at : DifferentiableAt ℝ ψ y := hψ_diff y hy
      apply deriv_comp y hφ_diff_at hψ_diff_at

    have h_id_deriv1 : ∀ y ∈ Ioo c d, (deriv φ (ψ y)) * (deriv ψ y) = 1 := by
      intro y hy
      rw [← chain_deriv y hy, h_id_deriv y hy]
      simp

    have deriv_product : deriv φ (ψ y) * deriv ψ y = 1 := h_id_deriv1 y hy

    have asoc: z * deriv φ (ψ y) * deriv ψ y = z * (deriv φ (ψ y) * deriv ψ y) := by
      rw [mul_assoc]

    rw [asoc]
    rw [deriv_product]
    simp
