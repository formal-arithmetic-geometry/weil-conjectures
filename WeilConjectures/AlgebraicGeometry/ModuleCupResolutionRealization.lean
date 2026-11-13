/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupRealizationComplexData
public import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
import WeilConjectures.AlgebraicGeometry.ModuleCupResolutionExistence
import WeilConjectures.AlgebraicGeometry.ModuleCupResolutionAugmentation

/-! # Realizing a resolution pairing in the derived category

## References

* Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  globalPullbackMatesColimits cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

/-- Every resolution pairing has a cochain realization, and its derived morphism
has the same H-zero map as the canonical derived-to-ordinary tensor comparison
(Stacks, Tags 0FKU and 06YH). -/
theorem moduleCup_resolution_realization {F G : X.Modules} (D : CupResolutionPairing F G) :
    let F₀ := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F
    let G₀ := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let canonical := Functor.LaxMonoidal.μ DerivedCategory.Q F₀ G₀ ≫
      DerivedCategory.Q.map (DerivedCategory.moduleCup_singleTensorIso
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) F G).hom
    ∃ t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex,
      D.Realizes t ∧
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (D.derivedMap t) =
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map canonical := by
  dsimp only
  obtain ⟨t, ht⟩ := moduleCup_resolution_realization_exists D
  refine ⟨t, ht, ?_⟩
  apply congrArg ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map)
  unfold CupResolutionPairing.derivedMap CupAcyclicResolution.derivedAugmentation
  rw [Functor.LaxMonoidal.μ_natural_assoc]
  rw [← Functor.map_comp_assoc]
  rw [moduleCup_resolution_augmentation D t ht]
  rw [Functor.map_comp]
  rw [Category.assoc]
  have hcancel := IsIso.hom_inv_id D.target.derivedAugmentation
  unfold CupAcyclicResolution.derivedAugmentation at hcancel
  rw [hcancel, Category.comp_id]

end
end AlgebraicGeometry.Scheme.Modules
