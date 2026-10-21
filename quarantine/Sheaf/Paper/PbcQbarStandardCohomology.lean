/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Sheaf.Paper.PbcCohomologySheaves
public import Sheaf.Paper.IntegralTStructure
public import Sheaf.Paper.LocalizedTStructure

/-! # Standard cohomology at common finite coefficient stages

Source: Bhatt--Scholze, Section 6.8, Propositions 6.8.11 and 6.8.14;
blueprint cohomology-sheaf convention (blueprint: def-weil-derived-cohomology-sheaves).
This extends the recorded ambient and rational cohomology to the actual Qbar pair
category. Invertibility is required on the scheme, including the empty scheme.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (X : Scheme.{u}) [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The strictly full image of an integral standard class at some finite stage.
Source: BS 6.8.11 and 6.8.14 (blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcQbarStandardClass (upper : Bool) (n : ℤ) :
    ObjectProperty (pbcQbarCategory l Ω X) :=
  fun K ↦ ∃ (E : Padic.FiniteCoefficientFields l Ω) (L : pbcIntegralStage l Ω X E),
    (if upper then (pbcIntegralTStructure X l (pbcFiniteField.{u} l Ω E)).le n L
      else (pbcIntegralTStructure X l (pbcFiniteField.{u} l Ω E)).ge n L) ∧
    Nonempty (K ≅ ((pbcScalarSystem l Ω X hDim.out hInv.out).ι E).obj
      ((pbcStageLocalization l Ω X E).obj L))

/-- The standard common-stage t-structure is uniquely fixed by the integral image classes.
Source: BS 6.8.11 and 6.8.14 (blueprint: def-weil-derived-cohomology-sheaves).
Proof: the localized standard t-structure has the strictly full integral image classes.
Finite scalar extension is finite free and t-exact, so its truncations commute with
coefficient extension, including identity extensions. Descend these truncations and
truncation triangles to the pair category. Orthogonality is checked at a common
finite field, where opposite bounds have zero Hom. Every object has finite bounds
at its displayed stage. These indexed classes determine the t-structure uniquely.
The cohomology of an integral representative is its ordinary ambient cohomology
placed in degree zero, rationalized and included at that same finite stage. -/
theorem pbcQbarStandardT_existsUnique :
    ∃! t : Triangulated.TStructure (pbcQbarCategory l Ω X),
      (∀ n : ℤ, t.le n = pbcQbarStandardClass l Ω X true n ∧
        t.ge n = pbcQbarStandardClass l Ω X false n) ∧ t.bounded = ⊤ := by
  sorry

/-- The standard t-structure determined by its integral cohomological bounds.
Source: BS 6.8.14 (blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcQbarStandardT : Triangulated.TStructure (pbcQbarCategory l Ω X) :=
  (pbcQbarStandardT_existsUnique l Ω X).exists.choose

/-- Degree-n cohomology, placed in the standard heart inside the Qbar derived category.
It is the two canonical truncations followed by the cohomological shift.
Source: BS 6.8.11 and 6.8.14 (blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcQbarCohomology (n : ℤ) : pbcQbarCategory l Ω X ⥤ pbcQbarCategory l Ω X :=
  (pbcQbarStandardT l Ω X).truncLE n ⋙ (pbcQbarStandardT l Ω X).truncGE n ⋙
    shiftFunctor (pbcQbarCategory l Ω X) n

end AlgebraicGeometry.Scheme
