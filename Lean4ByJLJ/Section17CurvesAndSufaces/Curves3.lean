import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Order.Interval.Set.Defs

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
example (φ : ℝ → ℝ) (ψ : ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hφ : ∀ x, x ∈ Set.Icc a b → φ x ∈ Set.Icc c d)
    (hψ : ∀ y, y ∈ Set.Icc c d → ψ y ∈ Set.Icc a b)
    (left_inv : ∀ x, x ∈ Set.Icc a b → ψ (φ x) = x)
    (right_inv : ∀ y, y ∈ Set.Icc c d → φ (ψ y) = y)
    (hφdiff : ContDiffOn ℝ ⊤ φ (Set.Icc a b))
    (hφregular : ∀ x, x ∈ Set.Icc a b → fderiv ℝ φ x ≠ 0) :
    ContDiffOn ℝ ⊤ ψ (Set.Icc c d) ∧
      ∀ y, y ∈ Set.Icc c d → ∀ z, fderiv ℝ ψ y (fderiv ℝ φ (ψ y) z) = z := by

      have hψ_hom : ∀ y ∈ Set.Icc c d, ∃ z ∈ Set.Icc a b, φ z = y := by
        intro y hy
        use ψ y
        constructor
        apply hψ at hy
        exact hy
        apply right_inv at hy
        exact hy

      have φ_injective_on_Icc : Set.InjOn φ (Set.Icc a b) := by
        intro x hx y hy hxy
        apply left_inv at hx
        rw [hxy] at hx
        apply left_inv at hy
        rw [← hx]
        exact hy
      have φ_inv_of_ψ : Set.InvOn φ ψ (Set.Icc c d) (Set.Icc a b) := by
        constructor
        exact right_inv
        exact left_inv

      have RR_hom : ℝ ≃ₜ ℝ := by
        exact Homeomorph.refl ℝ

      have φ'regular : ∀ x ∈ Set.Icc a b, φ' x ≠ 0 := by
        intro x hx
        apply hφregular
        exact hx


      have hψdiff : ContDiffOn ℝ ⊤ ψ (Icc c d) := by
        apply Homeomorph.contDiff_symm_deriv RR_hom φ'regular hψ_hom φ_injective_on_Icc φ_inv_of_ψ

      constructor
      exact hψdiff

      /-proof of the second part
      -/




      intro y hy
      have hyab : ψ y ∈ Icc a b := hψ y hy
      have hφreg : fderiv ℝ φ (ψ y) ≠ 0 := hφregular (ψ y) (hψ y hy)
      have hφψ : φ (ψ y) = y := right_inv y hy
      cases' hy with hcy hdy
      cases' lt_or_eq_of_le hdy with hdy_lt hdy_eq
      cases' lt_or_eq_of_le hcy with hcy_lt hcy_eq
      cases' hyab with hyab_a hyab_b
      cases' lt_or_eq_of_le hyab_a with hyab_a_lt hyab_a_eq
      cases' lt_or_eq_of_le hyab_b with hyab_b_lt hyab_b_eq



      have hψdiff_at : ContDiffAt ℝ ⊤ ψ y := by
        /-cases' hy with hcy hdy-/
        apply ContDiffOn.contDiffAt
        exact hψdiff
        simp
        constructor
        exact hcy_lt
        exact hdy_lt
        /-cases' lt_or_eq_of_le hdy with hdy_lt hdy_eq
        cases' lt_or_eq_of_le hcy with hcy_lt hcy_eq
        exact hcy_lt
        exact hdy_lt
        -/


      have hψy : HasStrictFDerivAt ψ (fderiv ℝ ψ y) y := by
        apply ContDiffAt.hasStrictFDerivAt
        exact hψdiff_at
        simp

      have hφψdiff_at : ContDiffAt ℝ ⊤ φ (ψ y) := by
        apply ContDiffOn.contDiffAt
        exact hφdiff
        simp
        constructor
        exact hyab_a_lt
        exact hyab_b_lt
        /-
        cases' hyab with hyab_a hyab_b
        cases' lt_or_eq_of_le hyab_a with hyab_a_lt hyab_a_eq
        cases' lt_or_eq_of_le hyab_b with hyab_b_lt hyab_b_eq
        simp
        constructor
        exact hyab_a_lt
        exact hyab_b_lt
        -/



      have hφψy : HasStrictFDerivAt φ (fderiv ℝ φ (ψ y)) (ψ y) := by
        apply ContDiffAt.hasStrictFDerivAt
        exact hφψdiff_at
        /-dont know why simp doesnt work at here-/

      have fderiv_id: (fderiv ℝ ψ y) ∘ ((fderiv ℝ φ (ψ y))) = id := by
        have h_comp := HasStrictFDerivAt.comp_hasStrictDerivAt hψy hφψy
        exact h_comp

      have fderiv_id' : ∀ z, fderiv ℝ ψ y (fderiv ℝ φ (ψ y) z) = z := by
        intro z
        have h_comp := congr_fun fderiv_id z
        exact h_comp

      exact fderiv_id'

      have hψ_deriv : HasFDerivAt ψ (fderiv ℝ ψ y) y := by
        apply DifferentiableOn.hasFDerivAt
        apply ContDiffOn.differentiableOn hψdiff
        simp
        rw [mem_nhds_iff]
        have cd_open: y ∈ (Set.Ioo c d) := by
          rw [Set.mem_Ioo]
          constructor
          exact hcy_lt
          exact hdy_lt
        let t := Ioo (c) (d)
        use t
        have t_y: y ∈ t := by exact cd_open
        have t_subset: t ⊆ Icc c d := by
          rw [Set.subset_def]
          intro x hx
          rw [Set.mem_Ioo] at hx
          rw [Set.mem_Icc]
          cases' hx with hcx hdx
          constructor
          linarith
          linarith
        have t_open: IsOpen t := by
          have h_open: IsOpen (Ioo c d) := by
            exact isOpen_Ioo
          exact h_open

        exact And.intro t_subset (And.intro t_open t_y)

      have hφψdiff_at : ContDiffAt ℝ ⊤ φ (ψ y) := by
        apply ContDiffOn.contDiffAt
        exact hφdiff
        simp
        constructor
        exact hyab_a_lt
        /- This wont work-/

      have hφψy : HasStrictFDerivAt φ (fderiv ℝ φ (ψ y)) (ψ y) := by
        apply ContDiffAt.hasStrictFDerivAt
        exact hφψdiff_at
























































/-
      have hφ_local_inv : ∀ x ∈ Set.Icc a b, HasFDerivAt φ (fderiv ℝ φ x) x := by
        intro x hx
        apply DifferentiableOn.hasFDerivAt
        apply ContDiffOn.differentiableOn hφdiff
        simp
        rw [mem_nhds_iff]
        cases' hx with hax hbx

      constructor
      apply ContDiffOn.of_local_inverse

      intro y hy z
      have hφψ : φ (ψ y) = y := right_inv y hy
      have hψφ : ψ (φ (ψ y)) = ψ y := congr_arg ψ hφψ
      rw [left_inv (ψ y) (hψ y hy)] at hψφ

      have hψ_deriv : HasFDerivAt ψ (fderiv ℝ ψ y) y := by
        apply DifferentiableOn.hasFDerivAt
        apply ContDiffOn.differentiableOn hψdiff
        simp
        rw [mem_nhds_iff]
        cases' hy with hcy hdy

      have hφ_deriv : HasFDerivAt φ (fderiv ℝ φ (ψ y)) (ψ y) := by
        apply hφ_local_inv
        apply hψ
        exact hy
-\


/-
Heather Macbeth: @Kevin Buzzard This is a toy case of the inverse function theorem,
but you might need to glue together several related results. Some starting points:
docs#ContDiffAt.to_localInverse, docs#HasStrictFDerivAt.localInverse_unique

Heather Macbeth: If you want to construct the inverse, and you want to avoid invoking
the inverse function theorem on Banach spaces, you can also route through order theory
for a purely one-dimensional construction. Look at the construction of docs#Real.arctan
for a model; it uses docs#StrictMonoOn.orderIso
-/
