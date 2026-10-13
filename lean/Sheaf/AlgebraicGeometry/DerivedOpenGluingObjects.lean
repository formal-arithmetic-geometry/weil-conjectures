/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction

/-! # Gluing derived complexes and compatible morphisms on two opens

Source: literature/stacks-project/cohomology.tex, Tag 08DG (Lemma 20.45.1)
(blueprint: lem-sc-derived-open-gluing-objects).
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
/-- Objects of the derived category glue across a two-open cover with their prescribed
transition, without an assertion about morphisms into another object.
Source: Stacks Project, Cohomology, Tag 08DG, first assertion and cone construction
(blueprint: lem-sc-derived-open-gluing-objects).
Proof: let W = U ∩ V. Form the difference of the two restriction maps from
Rj_U A ⊕ Rj_V B to Rj_W (B|W), using c on the first summand. Complete this
map to a distinguished triangle with first object F. Restrict the triangle to U.
Tag 08FE identifies the other two pushforwards with the same Rj from W to U;
the second component of the map is minus the identity. The resulting split
triangle identifies F|U with A. Interchanging U and V gives F|V ≅ B.
Restrict both projections to W: the kernel equation for the difference map
identifies their transition with c. The displayed canonical comparisons include
the units of the open-subscheme equivalences, so this equation is exactly the
one in the conclusion. The construction also works if an open or W is empty. -/
theorem derived_open_gluing_objects
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.obj A ≅
      (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.obj B) :
    ∃ (F : schemeDerivedCategory X)
      (iU : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj F ≅ A)
      (iV : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V)).mapDerivedCategory.obj F ≅ B),
      ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V)))).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left))
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
              (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (U ⊓ V))))).inv.app F ≫
        (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.map iU.hom ≫ c.hom =
      ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V)))).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv V).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right))
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
              (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (U ⊓ V))))).inv.app F ≫
        (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.map iV.hom := by sorry

end AlgebraicGeometry
