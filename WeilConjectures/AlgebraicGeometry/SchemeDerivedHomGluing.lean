/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.SchemeDerivedHomRestrictionTransport
import Mathlib.CategoryTheory.Localization.Equivalence

/-! # Gluing derived complexes and compatible morphisms on two opens

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

@[instance_reducible]
private noncomputable def derivedCategoryTransport
    {C D : Type u} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} D] (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] : HasDerivedCategory.{w} C := by
  let L := e.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  have hL : L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    apply Functor.IsLocalization.of_equivalence_source DerivedCategory.Q
      (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) L
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (e.symm.mapHomologicalComplex (ComplexShape.up ℤ))
    · intro K M f hf
      apply MorphismProperty.le_isoClosure
      change QuasiIso _
      have : QuasiIso f := hf
      change QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
      exact HomologicalComplex.quasiIso_map_of_preservesHomology f e.inverse
    · exact e.functor.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso
        (ComplexShape.up ℤ)
    · exact (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (e.mapHomologicalComplex (ComplexShape.up ℤ)).counitIso _ ≪≫
        Functor.leftUnitor _
  exact { D := DerivedCategory D, L := L }

private theorem lifted_morphism_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    (r : C ⥤ D) (e : D ⥤ E) [e.Full] [e.Faithful]
    (T : C ⥤ E) (q : T ≅ r ⋙ e) {F G : C} (f : F ⟶ G)
    (a : T.obj F ⟶ T.obj G)
    (h : r.map f = e.preimage (q.inv.app F ≫ a ≫ q.hom.app G)) :
    T.map f = a := by
  apply (cancel_epi (q.inv.app F)).mp
  apply (cancel_mono (q.hom.app G)).mp
  rw [Category.assoc, q.hom.naturality]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, Functor.comp_map]
  rw [h, Functor.map_preimage]
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
-- Additivity of the three-fold composite restriction functors exceeds the default size.
set_option maxHeartbeats 500000 in
-- Elaborating the restriction functors and their comparison isomorphisms needs this budget.
/-- Compatible local morphisms between two fixed global derived objects lift globally. -/
theorem scheme_derived_hom_gluing
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (F E : schemeDerivedCategory X) :
    let R_U := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R_V := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V)).mapDerivedCategory
    let S_U := (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory
    let S_V := (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory
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
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V)))) ≪≫
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
              (Scheme.Modules.overEquiv (U ⊓ V)))))
    let eV := ((Functor.mapDerivedCategoryCompIso
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
            (Scheme.Modules.overEquiv (U ⊓ V)))) ≪≫
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
              (Scheme.Modules.overEquiv (U ⊓ V)))))
    ∀ (a : R_U.obj F ⟶ R_U.obj E) (b : R_V.obj F ⟶ R_V.obj E),
      eU.inv.app F ≫ S_U.map a ≫ eU.hom.app E =
        eV.inv.app F ≫ S_V.map b ≫ eV.hom.app E →
      ∃ (f : F ⟶ E), R_U.map f = a ∧ R_V.map f = b := by
  dsimp only
  intro a b hab
  let eU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv U
  let eV : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ≌
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv V
  let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)) ≌
      SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv (U ⊓ V)
  let : HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    derivedCategoryTransport eU
  let : HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) :=
    derivedCategoryTransport eV
  let : HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V))) :=
    derivedCategoryTransport eW
  let rU := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let rV := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
  let rW := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (U ⊓ V)
  let qU := (Functor.mapDerivedCategoryCompIso rU eU.functor).symm
  let qV := (Functor.mapDerivedCategoryCompIso rV eV.functor).symm
  let qW := (Functor.mapDerivedCategoryCompIso rW eW.functor).symm
  let a' := eU.functor.mapDerivedCategory.preimage
    (qU.inv.app F ≫ a ≫ qU.hom.app E)
  let b' := eV.functor.mapDerivedCategory.preimage
    (qV.inv.app F ≫ b ≫ qV.hom.app E)
  have ha := scheme_derived_hom_restriction_transport.{u, w}
    X U (U ⊓ V) (homOfLE inf_le_left) F E a
  have hb := scheme_derived_hom_restriction_transport.{u, w}
    X V (U ⊓ V) (homOfLE inf_le_right) F E b
  have hc : derivedOpenHomRestriction X.toRingedSpace (homOfLE inf_le_left) a' =
      derivedOpenHomRestriction X.toRingedSpace (homOfLE inf_le_right) b' := by
    apply eW.functor.mapDerivedCategory.map_injective
    apply (cancel_epi (qW.hom.app F)).mp
    apply (cancel_mono (qW.inv.app E)).mp
    simpa only [Category.assoc] using ha.symm.trans (hab.trans hb)
  obtain ⟨_, _, hex⟩ :=
    derived_hom_mayer_vietoris.{u, w} X.toRingedSpace U V hcover F E
  obtain ⟨f, hf⟩ := (hex (a', b')).mp (sub_eq_zero.mpr hc)
  refine ⟨f, ?_, ?_⟩
  · exact lifted_morphism_eq rU.mapDerivedCategory eU.functor.mapDerivedCategory
      (rU ⋙ eU.functor).mapDerivedCategory qU f a (congrArg Prod.fst hf)
  · exact lifted_morphism_eq rV.mapDerivedCategory eV.functor.mapDerivedCategory
      (rV ⋙ eV.functor).mapDerivedCategory qV f b (congrArg Prod.snd hf)


end AlgebraicGeometry
