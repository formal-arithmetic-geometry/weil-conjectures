/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.OpenExtensionDerivedUnitIsIso
import all WeilConjectures.AlgebraicGeometry.DerivedOpenTensorHomBijective

/-! # Open extension counit on a derived tensor

## References

* Stacks Project, Tags 00A7, 08BS and 06YB.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable section
universe u w

local instance standardDerivedOpenExtensionTensorCounitIsIso (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- The counit of open extension is invertible on a tensor with an extended object.
(Stacks, Tags 08BS, 06YB, 06YH and 01AK) -/
theorem openExtension_tensor_counit_isIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∀ (J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
      (adj : J ⊣ R) (A : schemeDerivedCategory U.toScheme)
      (K : schemeDerivedCategory X), IsIso (adj.counit.app (J.obj A ⊗ K)) := by
  dsimp
  intro J adj A K
  let F := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let eU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Scheme.Modules.overEquiv U
  let E := eU.mapDerivedCategory
  have he (B L : schemeDerivedCategory X) :
      Function.Bijective (fun f : B ⟶ L ↦ (F ⋙ E.functor).map f) ↔
        Function.Bijective (fun f : B ⟶ L ↦ F.map f) :=
    (Functor.FullyFaithful.ofFullyFaithful E.functor).homEquiv.bijective
      |>.of_comp_iff' (fun f : B ⟶ L ↦ F.map f)
  have (B : schemeDerivedCategory U.toScheme) : IsIso (adj.unit.app B) :=
    openExtension_derived_unit_isIso X U J adj B
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app adj.unit
  have hJ := adj.fullyFaithfulLOfIsIsoUnit
  have := hJ.full
  have := hJ.faithful
  have hB : ∀ L : schemeDerivedCategory X,
      Function.Bijective (fun f : J.obj A ⟶ L ↦ F.map f) := by
    intro L
    exact (he (J.obj A) L).mp
      ((Scheme.hom_bijective_iff_counit adj (J.obj A)).mpr inferInstance L)
  have hs := (Scheme.raw_derived_hom_support X U (J.obj A)).mp hB
  have ht := (Scheme.raw_derived_hom_support X U (J.obj A ⊗ K)).mpr
    (fun x hx ↦ Scheme.tensor_stalk_vanishing X (J.obj A) K x (hs x hx))
  exact (Scheme.hom_bijective_iff_counit adj (J.obj A ⊗ K)).mp
    (fun L ↦ (he (J.obj A ⊗ K) L).mpr (ht L))

end
end AlgebraicGeometry
