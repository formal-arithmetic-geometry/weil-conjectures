/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Gluing derived complexes and compatible morphisms on two opens

Source: literature/stacks-project/cohomology.tex, Tag 08DG (Lemma 20.45.1)
(blueprint: lem-sc-scheme-derived-hom-restriction-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
-- Additivity of the three-fold composite restriction functors exceeds the default size.
set_option maxHeartbeats 1600000 in
-- Elaborating the restriction functors and their comparison isomorphisms needs this budget.
/-- Restricting a local derived morphism commutes with transporting from the localized
site to the open subscheme. The formula includes all derived composition comparisons.
Source: Stacks Project, Cohomology, Tag 08BW, canonical local Hom restriction maps;
Mathlib's equivalence Scheme.Modules.overEquiv
(blueprint: lem-sc-scheme-derived-hom-restriction-transport).
Proof: mapDerivedCategoryCompIso identifies restriction on the open subscheme with
restriction to the localized site followed by the derived equivalence. Transport a
back using the full and faithful derived equivalence and these identifications.
The underived comparison from iterated restriction to direct restriction cancels
the functor and inverse of overEquiv U using its unit. After deriving, the unit
naturality equation cancels the transported equivalence on the morphism a.
Associativity of the derived composition comparisons identifies what remains
with overFunctorMap followed by the equivalence for W. This is precisely the
conjugation defining derivedOpenHomRestriction. Conjugating by the outer
composition comparisons gives the displayed equality. This argument is natural
in F and E and works for W=U and W empty as well. -/
theorem scheme_derived_hom_restriction_transport
    (X : Scheme.{u}) (U W : X.Opens) (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (F E : schemeDerivedCategory X) :
    let R_U := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let S_U := (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
            (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv W)).mapDerivedCategory
    let eU := ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
            (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv W))).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
              (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv W))))
    let e := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let eW := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
      (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv W)
    let qU := Functor.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) e
    let qW := Functor.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W) eW
    ∀ (a : R_U.obj F ⟶ R_U.obj E),
      eU.inv.app F ≫ S_U.map a ≫ eU.hom.app E =
        qW.hom.app F ≫ eW.mapDerivedCategory.map
          (derivedOpenHomRestriction X.toRingedSpace i
            (e.mapDerivedCategory.preimage (qU.inv.app F ≫ a ≫ qU.hom.app E))) ≫
          qW.inv.app E := by sorry

end AlgebraicGeometry
