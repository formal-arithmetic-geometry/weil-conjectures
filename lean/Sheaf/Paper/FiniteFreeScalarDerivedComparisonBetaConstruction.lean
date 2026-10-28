/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralFiniteScalarModelDefinitions

/-! Existence of the normalized finite-free beta comparison.
(blueprint: new-sfb-finite-free-scalar-derived-comparison-beta-construction)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

/--
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md, formal-properties
paragraphs. Choose flat-term K-flat representatives, apply the restricted tensor
identification, and descend the augmentation comparison. This is the existence and
ordinary normalization part of the beta construction.
(blueprint: new-sfb-finite-free-scalar-derived-comparison-beta-construction)
-/
theorem finiteFreeScalarDerivedComparison_beta_construction
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X)) :
    ∃ β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
        scalarSixChange a Z ⋙ restriction a Z,
      ∀ Z, AugmentationNormalized a S t Z (β Z) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
