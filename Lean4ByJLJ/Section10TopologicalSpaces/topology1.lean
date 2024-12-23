import Mathlib.Tactic

namespace Section10sheet1

noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, the type `TopologicalSpace X` is the type of topologies on `X`.
`TopologicalSpace` is a structure; its four fields are one data field `IsOpen : Set X → Prop` (the
predicate on subsets of `X` saying whether or not they're open) and then three proof fields
(`isOpen_univ` saying the whole space is open, `isOpen_inter` saying the intersection of two
opens is open, and `isOpen_sUnion` saying an arbitrary union of opens is open).

Here is a simple example: let's make the discrete topology on a type.
-/

open TopologicalSpace

variable (X : Type)

set_option linter.unusedVariables false -- please stop moaning about unused variables

example : TopologicalSpace X where
  IsOpen (s : Set X) := True -- "Is `s` open? Yes, always"
  isOpen_univ := by
    -- is the whole space open? The goal is `True`
    trivial
  isOpen_inter := by
    -- let s and t be two sets
    intros s t
    -- assume they're open
    intros hs ht
    -- Is their intersection open?
    -- By definition, this means "can you prove `True`"?
    trivial
  isOpen_sUnion := by
    -- say F is a family of sets
    intro F
    -- say they're all open
    intro hF
    -- Is their union open?
    trivial

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ -- empty set or whole thing
  isOpen_univ := by
    dsimp
    right
    rfl -- use `dsimp`
  isOpen_inter := by
    intro  s t
    intro h1 h2
    cases' h1 with h11 h12
    cases' h2 with h21 h22
    left
    rw [h21]
    rw [h11]
    simp
    left
    rw [h11]
    simp
    cases' h2 with h21 h22
    left
    rw [h21]
    simp
    right
    rw [h22,h12]
    simp
     -- use `cases'`
  isOpen_sUnion := by
    intro F
    -- do cases on whether Set.univ ∈ F
    intro h1
    by_cases h : Set.univ ∈ F
    right
    aesop
    left
    by_contra! h2
    rcases h2 with ⟨s, hs1, hs2⟩
    specialize h1 hs1
    aesop



-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  simp

-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ

-- Let's make it from first principles.

def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  intro h1 h2
  use 1
  constructor
  linarith
  intro h3 h4
  simp

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
  simp at hx
  obtain ⟨ε₁, hε₁, hs⟩ := hs x (by aesop)
  obtain ⟨ε₂, hε₂, ht⟩ := ht x (by aesop)
  use min ε₁ ε₂, by positivity
  rintro y ⟨h1,h2⟩
  simp
  constructor
  apply hs
  constructor
  have foo : min ε₁ ε₂ ≤ ε₁ := min_le_left ε₁ ε₂
  linarith
  have foo : min ε₁ ε₂ ≤ ε₁ := min_le_left ε₁ ε₂
  linarith
  apply ht
  constructor
  have foo : min ε₁ ε₂ ≤ ε₂ := min_le_right ε₁ ε₂
  linarith
  have foo : min ε₁ ε₂ ≤ ε₂ := min_le_right ε₁ ε₂
  linarith





lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x hx
  simp at *
  rcases hx with ⟨t,htf,htx⟩
  obtain ⟨ε, hε, h⟩ := hF t htf x htx
  use ε
  constructor
  exact hε
  intro y
  simp at h
  intro hy1 hy2
  use t
  constructor
  exact htf
  apply h at hy1
  apply hy1 at hy2
  exact hy2




-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
