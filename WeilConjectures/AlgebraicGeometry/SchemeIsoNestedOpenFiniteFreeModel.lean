/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Transport of a finite-free model from a nested open

## References

* [Stacks Project, Tag 08EE](https://stacks.math.columbia.edu/tag/08EE)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option maxHeartbeats 500000 in
-- The nested functor comparisons require additional definitional equality checks.
set_option backward.isDefEq.respectTransparency false in
/-- Transport one specified bounded-above finite-free model on a nested open across a
scheme isomorphism. Neither scheme is assumed affine, and no module localization is used. -/
theorem exists_scheme_iso_nested_open_finite_free_model
    {X Y : Scheme.{u}} (s : X ≅ Y) (U : X.Opens)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (C : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (D : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hC : Nonempty (C ≅
      ((Modules.restrictFunctor s.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj D))
    (V : U.toScheme.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings U.toScheme.toRingedSpace).over V) (ULift.{u} (Fin r))))
    (hiso : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.obj
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj (DerivedCategory.Q.obj C)) ≅
        DerivedCategory.Q.obj P)) :
    ∃ W : Y.Opens,
      (∀ y : X, s.hom y ∈ W ↔ ∃ hy : y ∈ U, (⟨y, hy⟩ : U.toScheme) ∈ V) ∧
      ∃ P' : CochainComplex
          (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W)) ℤ,
        (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P'.X i)) ∧
        (∀ i : ℤ, ∃ r : ℕ, Nonempty (P'.X i ≅ SheafOfModules.free
          (R := (moduleRings Y.toRingedSpace).over W) (ULift.{u} (Fin r)))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings Y.toRingedSpace) W).mapDerivedCategory.obj
            (DerivedCategory.Q.obj D) ≅ DerivedCategory.Q.obj P') := by
  classical
  let j := U.ι ≫ s.hom
  let W := j ''ᵁ V
  let a := j.isoImage V
  let EV := Modules.overEquiv V
  let EW := Modules.overEquiv W
  let ES := CategoryTheory.Equivalence.mk
    (Modules.restrictFunctor a.inv) (Modules.restrictFunctor a.hom)
    ((Modules.restrictFunctorComp a.hom a.inv).symm ≪≫
      Modules.restrictFunctorCongr a.hom_inv_id ≪≫ Modules.restrictFunctorId).symm
    ((Modules.restrictFunctorComp a.inv a.hom).symm ≪≫
      Modules.restrictFunctorCongr a.inv_hom_id ≪≫ Modules.restrictFunctorId)
  let A := (EV.trans ES).trans EW.symm
  have : A.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full A.functor
  let P' := (A.functor.mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨W, ?_, P', ?_, ?_, ?_⟩
  · intro y
    constructor
    · rintro ⟨z, hz, he⟩
      have he' : z.val = y := by
        apply s.hom.isOpenEmbedding.injective
        exact he
      subst y
      exact ⟨z.property, hz⟩
    · rintro ⟨hy, hV⟩
      exact ⟨⟨y, hy⟩, hV, rfl⟩
  · obtain ⟨N, hN⟩ := hb
    exact ⟨N, fun i hi ↦ A.functor.map_isZero (hN i hi)⟩
  · have unitIso : A.functor.obj
        (SheafOfModules.unit ((moduleRings U.toScheme.toRingedSpace).over V)) ≅
        SheafOfModules.unit ((moduleRings Y.toRingedSpace).over W) :=
      EW.inverse.mapIso ((Modules.restrictFunctor a.inv).mapIso
        (V.sheafOfModulesEquivOverUnit (moduleRings U.toScheme.toRingedSpace)) ≪≫
        Modules.restrictUnitIso a.inv) ≪≫
          W.sheafOfModulesEquivOverInverseUnit (moduleRings Y.toRingedSpace)
    intro i
    obtain ⟨r, ⟨e⟩⟩ := hfree i
    exact ⟨r, ⟨A.functor.mapIso e ≪≫
      (SheafOfModules.mapFreeIso A.functor (ULift.{u} (Fin r)) unitIso.symm).symm⟩⟩
  · let G : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
      SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      (Modules.overEquiv U).functor
    let R : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace) := Modules.restrictFunctor s.hom
    let GY := R ⋙ G
    let H := SheafOfModules.overFunctor.{u} (moduleRings U.toScheme.toRingedSpace) V
    let L := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) W
    have : G.Additive := Functor.additive_of_preserves_binary_products G
    let ER := CategoryTheory.Equivalence.mk R (Modules.restrictFunctor s.inv)
      ((Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
        Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Modules.restrictFunctorId).symm
      ((Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
        Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Modules.restrictFunctorId)
    have : R.IsEquivalence := ER.isEquivalence_functor
    have : R.Additive := Functor.additive_of_preserves_binary_products R
    have : GY.Additive := inferInstance
    have : H.Additive := Functor.additive_of_preserves_binary_products H
    have : L.Additive := Functor.additive_of_preserves_binary_products L
    have : A.functor.Additive := inferInstance
    let cG : GY ≅ Modules.restrictFunctor j :=
      Functor.isoWhiskerLeft R (Modules.overFunctorEquiv U) ≪≫
        (Modules.restrictFunctorComp U.ι s.hom).symm
    let c0 : (GY ⋙ H) ⋙ (EV.functor ⋙ ES.functor) ≅ L ⋙ EW.functor :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft GY ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (Modules.overFunctorEquiv V) ES.functor) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerRight cG _) _ ≪≫
        Functor.isoWhiskerRight (Modules.restrictFunctorComp V.ι j).symm ES.functor ≪≫
        (Modules.restrictFunctorComp a.inv (V.ι ≫ j)).symm ≪≫
        Modules.restrictFunctorCongr (j.isoImage_inv_ι V) ≪≫
        (Modules.overFunctorEquiv W).symm
    let c : (GY ⋙ H) ⋙ A.functor ≅ L :=
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c0 EW.inverse ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L EW.unitIso.symm ≪≫
          Functor.rightUnitor L
    obtain ⟨hC⟩ := hC
    obtain ⟨hiso⟩ := hiso
    let eC : (G.mapHomologicalComplex (.up ℤ)).obj C ≅
        (GY.mapHomologicalComplex (.up ℤ)).obj D :=
      (G.mapHomologicalComplex (.up ℤ)).mapIso hC ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl GY) (.up ℤ)).app D
    let eH : (H.mapHomologicalComplex (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj C) ≅
        ((GY ⋙ H).mapHomologicalComplex (.up ℤ)).obj D :=
      (H.mapHomologicalComplex (.up ℤ)).mapIso eC ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (GY ⋙ H)) (.up ℤ)).app D
    let q : DerivedCategory.Q.obj
        (((GY ⋙ H).mapHomologicalComplex (.up ℤ)).obj D) ≅ DerivedCategory.Q.obj P :=
      DerivedCategory.Q.mapIso eH.symm ≪≫
        (H.mapDerivedCategoryFactors.app _).symm ≪≫
        H.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app C).symm ≪≫ hiso
    exact ⟨L.mapDerivedCategoryFactors.app D ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).app D).symm ≪≫
      (A.functor.mapDerivedCategoryFactors.app _).symm ≪≫
      A.functor.mapDerivedCategory.mapIso q ≪≫ A.functor.mapDerivedCategoryFactors.app P⟩

end AlgebraicGeometry.Scheme
