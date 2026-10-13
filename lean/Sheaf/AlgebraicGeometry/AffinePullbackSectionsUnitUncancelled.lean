/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.AffinePullbackModelComparisonsIsIso

/-! # Pullback unit on affine sections models

Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: new-affine-pullback-sections-model-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

set_option synthInstance.maxHeartbeats 100000 in
-- Affine carrier identifications require additional instance search.
set_option maxHeartbeats 800000 in
-- Affine carrier identifications require additional elaboration heartbeats.
/-- Before cancelling comparisons, the normalized derived pullback unit agrees with
its ordinary model. This identity holds for every complex, without K-flatness.
Source: Stacks Project, perfect.tex, Tag 0AA7, normalized derived unit calculation;
Mathlib CategoryTheory.Adjunction.derivedη_fac_app.
(blueprint: new-affine-pullback-sections-unit-uncancelled).
Proof: evaluate the normalized Hom equivalence in exists_schemeDerivedAdjunction
at the identity of termwise pullback of K. This factors the derived unit followed
by derived direct image of the fixed left-derived counit as the localized ordinary
unit followed by the direct-image right-derived unit. Apply derived R-sections and
precompose with its comparison. Naturality moves this comparison past the ordinary
unit. The factorization of rightDerivedFunctorCompUnit replaces the two successive
right-derived units by the composition unit. Naturality of r moves the counit past
r. Apply hr at the homotopy object of the termwise pullback. Naturality of the exact
restriction localization factors and of the sections comparison gives the right
side below. Finally Q/Qh transport naturality changes all homotopy maps into the
shown complex maps. This proves an equality of fixed morphisms and assumes no
comparison invertible; hence it also applies to zero complexes and arbitrary v
satisfying hr. It does not assert compatibility for an arbitrary isomorphism b. -/
theorem affinePullbackSections_unit_uncancelled
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    (v : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅
      affineGlobalSections (𝟙 (Spec B)) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (r : schemeDerivedDirectImage g ⋙ affineDerivedGlobalSections (𝟙 (Spec R)) ≅
      affineDerivedGlobalSections (𝟙 (Spec B)) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory)
    (hr : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
          (affineGlobalSections (𝟙 (Spec R)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
          ((schemeDerivedDirectImage g).obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (𝟙 (Spec B)) ⋙
          ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
            (affineGlobalSections (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) ≪≫
          Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J))
    [(Scheme.Modules.tensorPullback g).Additive]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)) ℤ) :
    let P := Scheme.Modules.tensorPullback g
    let U := ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
    let adjP := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
    let PK := (P.mapHomologicalComplex (.up ℤ)).obj K
    let Y := ((affineGlobalSections (𝟙 (Spec B))).mapHomologicalComplex (.up ℤ)).obj PK
    affineModelSectionsComparison R K ≫
        (affineDerivedGlobalSections (𝟙 (Spec R))).map
          ((canonicalPullbackAdjunction g).unit.app (DerivedCategory.Q.obj K)) ≫
        r.hom.app ((derivedPullback g).obj (DerivedCategory.Q.obj K)) ≫
        U.mapDerivedCategory.map
          ((affineDerivedGlobalSections (𝟙 (Spec B))).map
            (affineModelPullbackComparison g K)) =
      DerivedCategory.Q.map
        (((affineGlobalSections (𝟙 (Spec R))).mapHomologicalComplex (.up ℤ)).map
            ((adjP.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
          (v.hom.mapHomologicalComplex (.up ℤ)).app PK) ≫
        U.mapDerivedCategoryFactors.inv.app Y ≫
        U.mapDerivedCategory.map (affineModelSectionsComparison B PK) := by sorry

end AlgebraicGeometry
