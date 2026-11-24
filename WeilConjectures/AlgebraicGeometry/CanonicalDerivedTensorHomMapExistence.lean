/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescent
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality

/-! # Normalized derived tensor-Hom maps

## References

* Stacks Project, Tags 08DJ and 0A90
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uCD wCD
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Existence of normalized natural uncurrying maps, without asserting bijectivity
(Stacks, Tags 08DJ and 0A90). -/
theorem exists_canonicalDerivedTensorHomMap (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))] :
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      IsCanonicalDerivedTensorHomMap X t := by
  obtain ⟨t, ht, hi⟩ := exists_tensorHomUncurry_descent X
  refine ⟨t, tensorHomUncurry_descent_natural X t ht hi, ?_⟩
  intro P L M hP φ
  refine ⟨schemeTensorHomUncurry X P L M φ, ?_, ht P L M hP φ⟩
  intro p q n h h'
  exact schemeTensorHomUncurry_component X P L M φ p q n h h'

end AlgebraicGeometry
