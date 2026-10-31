/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.NormalizedCoefficientFamilies
import WeilConjectures.AlgebraicGeometry.CbcCompletedPullCoefficientFamilyCompatibility

/-! # Strict completed-pullback coefficient family argument

Source: current blueprint, coefficient coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The actual strict completed pullback has a normalized exact coefficient family.

(blueprint: lem-cbc-normalized-pull-family-existence)

Proof: apply the two strict subarguments. The first supplies preservation, the
coherent exact family and its localization equality. The second supplies the
scalar comparison, completion-unit equation, beta equation and repeated-field
unit. Assemble these fields into the published family.
-/
theorem cbcCompletedPullCoefficientFamily_exists (g : Y ⟶ X) :
    Nonempty (CbcCompletedPullCoefficientFamily l Ω g) := by
  obtain ⟨C⟩ := cbcCompletedPullCoefficientFamilyCore_exists l Ω g
  obtain ⟨D⟩ := cbcCompletedPullCoefficientFamilyCompatibility_exists l Ω C
  exact ⟨{
    preserves := C.preserves
    family := C.family
    localization := C.localization
    comparison := fun {E F} h => (D.comparison (E := E) (F := F) h).hom
    completionUnit := fun h K => D.completionUnit h K
    beta := fun {E F} h K => D.beta h K
    unit := D.unit
  }⟩

end AlgebraicGeometry.Scheme
