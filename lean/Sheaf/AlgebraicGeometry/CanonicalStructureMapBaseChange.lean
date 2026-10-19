/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapAlgebra

/-! # Canonical structure maps and derived exchange

Source: Stacks Project, Tag 08HY, the mate description, and Tag 0096.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- Comparing the two sheaf adjunctions requires unfolding their common right adjoint.
private theorem tensor_structure_transport {A B : Scheme.{u}} (k : A ⟶ B) :
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction k)).hom.app
        (SheafOfModules.unit B.ringCatSheaf) ≫
      SheafOfModules.pullbackObjUnitToUnit k.toRingCatSheafHom =
    Scheme.Modules.tensorPullbackObjUnitToUnit k := by
  apply (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).homEquiv _ _
    |>.injective
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_apply]
  simp only [← Adjunction.homEquiv_apply,
    Scheme.Modules.tensorPullbackObjUnitToUnit,
    Equiv.apply_symm_apply]
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    k.toRingCatSheafHom

set_option maxHeartbeats 800000 in
-- The naturality square involves localization of the sheaf single-complex comparisons.
private theorem single_pullback_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : Scheme.{u}} (k : A ⟶ B) {M N : B.Modules} (a : M ⟶ N) :
    (derivedPullback k).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
        Scheme.Modules.canonicalSinglePullbackMap k N =
      Scheme.Modules.canonicalSinglePullbackMap k M ≫
        (DerivedCategory.singleFunctor _ 0).map ((Scheme.Modules.pullback k).map a) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := Scheme.Modules.canonicalTensorPullbackAdditive k
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k
  let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction k)
  have hε := ε.naturality ((HomotopyCategory.singleFunctor _ 0).map a)
  have hc := (HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.tensorPullback k) (ComplexShape.up ℤ) 0).hom.naturality a
  have ht := t.hom.naturality a
  simp only [Scheme.Modules.canonicalSinglePullbackMap,
    DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, Functor.comp_map, Functor.comp_obj,
    Category.assoc] at hε ⊢
  erw [reassoc_of% hε]
  simp only [← Functor.map_comp]
  congr 2
  erw [Functor.mapHomotopyCategory_map]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp]
  congr 1
  simp only [Functor.comp_map] at hc
  erw [reassoc_of% hc, ← Functor.map_comp, ht, Functor.map_comp]

set_option maxHeartbeats 800000 in
-- The right-derived unit is compared with localized single-complex morphisms.
private theorem single_directImage_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : Scheme.{u}} (k : A ⟶ B) {M N : A.Modules} (a : M ⟶ N) :
    Scheme.Modules.canonicalSingleDirectImageMap k M ≫
        (schemeDerivedDirectImage k).map ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings A.toRingedSpace)) 0).map a) =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings B.toRingedSpace)) 0).map
          ((Scheme.Modules.pushforward k).map a) ≫
        Scheme.Modules.canonicalSingleDirectImageMap k N := by
  let β := (RingedSpace.moduleDirectImage k.toLRSHom.toShHom).rightDerivedFunctorUnit
  have hβ := β.naturality ((HomotopyCategory.singleFunctor _ 0).map a)
  have hc := (HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.pushforward k) (ComplexShape.up ℤ) 0).inv.naturality a
  simp only [Scheme.Modules.canonicalSingleDirectImageMap,
    DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, Functor.comp_map, Functor.comp_obj,
    Category.assoc] at hβ ⊢
  erw [← hβ]
  erw [Functor.mapHomotopyCategory_map]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp]
  congr 1
  congr 2
  simp only [Functor.comp_map] at hc
  exact hc.symm

set_option maxHeartbeats 800000 in
-- Naturality rewrites elaborate the selected derived functors and localization maps.
/-- The canonical structure maps commute with the pinned derived exchange map.
No cartesianness, flatness, vanishing or invertibility assumption is needed.
Source: Stacks Project, Tag 08HY, mate description, and Tag 0096, pullback of modules.
(blueprint: lem-sc-canonical-structure-map-base-change).

Proof: Represent each structure map as the single of the ordinary structure map
followed by the canonical right-derived unit. Apply derivedBaseChange_unit_compatibility
at the homotopy single of O_X. Naturality of the single-complex pullback and pushforward
comparisons moves these comparisons through the ordinary exchange. The last clause of
moduleBaseChangeMap_algebra is the ordinary identity:
tensorPullback g applied to f sharp, followed by ordinary exchange and pushforward
of tensorPullbackObjUnitToUnit p, equals tensorPullbackObjUnitToUnit g followed by
f' sharp. It follows by transposition from p f = f' g, using the adjunction triangles.
Localize the single of this identity. Naturality of the right-derived unit moves the
p-structure map to its target, and naturality of the left-derived counit moves f sharp
to its source. The comparisons from tensor to ordinary pullback are the unique maps
preserving the common pushforward adjunction;
therefore canonicalSingleAdjunctionTranspose identifies the remaining composites with
the displayed canonical single maps. Reassociate to obtain the equation. This proof
also applies to empty schemes, where the same functorial and triangle identities hold. -/
theorem canonical_structure_map_base_change
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) :
    (derivedPullback g).map
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          Scheme.Modules.canonicalSingleDirectImageMap f
            (SheafOfModules.unit X.ringCatSheaf)) ≫
      (schemeDerivedBaseChangeMap f f' g p h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit X.ringCatSheaf)) ≫
        (schemeDerivedDirectImage f').map
          (Scheme.Modules.canonicalSinglePullbackMap p
              (SheafOfModules.unit X.ringCatSheaf) ≫
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map
                (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom))) =
    (Scheme.Modules.canonicalSinglePullbackMap g (SheafOfModules.unit S.ringCatSheaf) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)) ≫
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) ≫
        Scheme.Modules.canonicalSingleDirectImageMap f'
          (SheafOfModules.unit X'.ringCatSheaf)) := by
  let tg := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction g)
  let tp := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction p)
  let b := tg.inv.app ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf)) ≫
    Scheme.Modules.moduleBaseChangeMap f f' g p h (SheafOfModules.unit X.ringCatSheaf) ≫
    (Scheme.Modules.pushforward f').map (tp.hom.app (SheafOfModules.unit X.ringCatSheaf))
  have hb : (Scheme.Modules.pullback g).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫ b ≫
      (Scheme.Modules.pushforward f').map
        (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom) =
      SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom ≫
        SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom := by
    apply (cancel_epi (tg.hom.app (SheafOfModules.unit S.ringCatSheaf))).mp
    dsimp only [b]
    simp only [Category.assoc]
    erw [← tg.hom.naturality_assoc]
    erw [Iso.hom_inv_id_app_assoc]
    erw [← Functor.map_comp, tensor_structure_transport p,
      reassoc_of% (tensor_structure_transport g)]
    obtain ⟨mu, mu', _, _, _, _, he⟩ :=
      Scheme.Modules.moduleBaseChangeMap_algebra f f' g p h
    simpa only [Category.assoc] using he
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (Scheme.Modules.canonicalSingleBaseChangeComparison
    f f' g p h (SheafOfModules.unit X.ringCatSheaf))]
  erw [single_directImage_naturality f'
    (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)]
  erw [reassoc_of% (single_pullback_naturality g
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  erw [hb]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry
