/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom

/-!
# The derived extension of scalars of a flat sheaf placed in degree zero

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel. For a
flat étale sheaf of `Λ`-modules `F`, the unit `F ⟶ Res (Λ' ⊗_Λ F)` of extension of scalars,
placed in degree zero, exhibits `(Λ' ⊗_Λ F)[0]` as the derived base change of `F[0]`
(`AlgebraicGeometry.Etale.isDerivedBaseChange_singleFunctor_map_unit`): `F[0]` is K-flat, so its
derived base change is computed by the underived extension of scalars
(`CategoryTheory.Functor.ReductionDatum.bijective_comp_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

/-- Sheaves of modules on the small étale site have colimits of discrete shapes in `Type`.
Instance search times out on this. -/
local instance (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (S : Type) :
    HasColimitsOfShape (Discrete S) (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (inferInstance : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))).has_colimits_of_shape _

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'}
  (hρ : Function.Surjective ρ) {a : Λ} (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u})

set_option synthInstance.maxHeartbeats 200000 in
-- the flatness and K-flatness instances of the single complexes are found by a long search
include hρ ha in
/-- **The derived base change of a flat sheaf in degree zero is its extension of scalars**: for
a flat étale sheaf of `Λ`-modules `F`, the unit `F ⟶ Res (Λ' ⊗_Λ F)` of extension of scalars,
placed in degree zero, exhibits `(Λ' ⊗_Λ F)[0]` as the derived base change of `F[0]`. -/
lemma isDerivedBaseChange_singleFunctor_map_unit
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : ObjectProperty.flat F) :
    Sheaf.IsDerivedBaseChange ((DerivedCategory.singleFunctor _ 0).map
        ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit.app F) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
        _) := by
  have := Sheaf.restrictScalars_full X.smallEtaleTopology ρ hρ
  let D := Sheaf.extendScalarsReductionDatum X.smallEtaleTopology hρ ha
  let P := (HomologicalComplex.single (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (.up ℤ) 0).obj F
  have hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P :=
    (CochainComplex.kFlat_single_obj_iff_flat _ 0).2 hF
  have h : Sheaf.IsDerivedBaseChange (DerivedCategory.Q.map (D.complexMap P) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactors.inv.app
        ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P)) :=
    fun N ↦ D.bijective_comp_map P hP N
  let e := DerivedCategory.Q.mapIso
    (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapCochainComplexSingleFunctor 0).app F)
  have hc : D.complexMap P ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)).map
        (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapCochainComplexSingleFunctor 0).hom.app
          F) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapCochainComplexSingleFunctor 0).hom.app _ =
      (HomologicalComplex.single _ (.up ℤ) 0).map
        ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit.app F) := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapCochainComplexSingleFunctor, HomologicalComplex.single_map_f_self,
      D.complexMap_f]
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.whiskeringRight_obj_obj,
      Sheaf.extendScalarsReductionDatum, HomologicalComplex.singleMapHomologicalComplex,
      NatIso.ofComponents_hom_app, ↓reduceDIte, eqToHom_refl, Functor.id_obj,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl,
      Iso.refl_hom, Iso.refl_inv, Category.id_comp, D]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have key : (DerivedCategory.singleFunctor _ 0).map
        ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit.app F) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
        _ = (DerivedCategory.Q.map (D.complexMap P) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactors.inv.app
        ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map e.hom := by
    refine (cancel_mono
      (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).hom.app
        ((Sheaf.extendScalars X.smallEtaleTopology ρ).obj F))).1 ?_
    have n₁ := Functor.mapDerivedCategoryFactors_inv_naturality
      (Sheaf.restrictScalars X.smallEtaleTopology ρ)
      (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapCochainComplexSingleFunctor 0).hom.app F)
    have n₂ := Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      (Sheaf.restrictScalars X.smallEtaleTopology ρ)
      ((Sheaf.extendScalars X.smallEtaleTopology ρ).obj F)
    have s₂ : DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map
          ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit.app F)) =
        DerivedCategory.Q.map (D.complexMap P) ≫ DerivedCategory.Q.map
          (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)).map
            (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapCochainComplexSingleFunctor
              0).hom.app F)) ≫ DerivedCategory.Q.map
            (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapCochainComplexSingleFunctor
              0).hom.app _) := by
          rw [← Functor.map_comp, ← Functor.map_comp, hc]
    have s₃ : DerivedCategory.Q.map (D.complexMap P) ≫ DerivedCategory.Q.map
          (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)).map
            (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapCochainComplexSingleFunctor
              0).hom.app F)) ≫ DerivedCategory.Q.map
            (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapCochainComplexSingleFunctor
              0).hom.app _) = DerivedCategory.Q.map (D.complexMap P) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactors.inv.app
          ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map e.hom ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor
          0).hom.app ((Sheaf.extendScalars X.smallEtaleTopology ρ).obj F) := by
      rw [← n₂]
      erw [reassoc_of% n₁]
      rfl
    simp only [Category.assoc, Iso.inv_hom_id_app]
    refine (Category.comp_id _).trans ((s₂.trans s₃).trans ?_)
    simp only
  rw [key]
  exact h.comp_map_iso e

end AlgebraicGeometry.Etale
