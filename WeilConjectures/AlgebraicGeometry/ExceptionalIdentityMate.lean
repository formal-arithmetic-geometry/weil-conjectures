/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-! Canonical exceptional tensor extraction and its projection/counit coherence. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
/--
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md
Step 4(iii): identity normalization of the specified exceptional and pullback comparisons
in the projection/counit tensor passage. -/
theorem exceptionalIdentityMate (T : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    lowerShriekRightAdjointTensorMap (rightDerivedUpperShriekAdjunction Λ (𝟙 T)) K L ≫
        (rightDerivedUpperShriekIdIso Λ T).hom.app
          (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj K).obj L) =
      derivedTensorHom (ModuleCat.{u + 1} Λ)
        ((rightDerivedUpperShriekIdIso Λ T).hom.app K)
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) T).hom.app L) := by
  sorry
end AlgebraicGeometry.Etale
