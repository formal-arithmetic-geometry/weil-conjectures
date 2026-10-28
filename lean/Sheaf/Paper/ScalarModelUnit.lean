/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.Paper.DivisibleExtensionDerivedReduction
import all Sheaf.Paper.DivisibleExtensionDerivedReduction
/-! # Uniqueness and the arbitrary-complex unit of scalar extension -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} {R R' : Sheaf J CommRingCat.{r}} {φ : R ⟶ R'}

private theorem ordinary_unit_eq (S : ScalarData.{c, v, r} φ) :
    S.ordinaryAdjunction.unit = (SheafOfModules.sheafScalarOrdinaryAdjunction φ S.model).unit := by
  ext M U x
  have hs := S.unit_section M U x
  have hc := (Classical.choose_spec
    (SheafOfModules.sheafDerivedScalarAdjunction_exists φ S.model)).1 M U x
  have hi (y : (S.model.E.obj M).val.obj U) :
      (eqToHom (S.model.obj_eq M).symm).val.app U
        ((eqToHom (S.model.obj_eq M)).val.app U y) = y :=
    congrArg (fun a ↦ a.val.app U y) (eqToIso (S.model.obj_eq M)).hom_inv_id
  calc
    _ = (eqToHom (S.model.obj_eq M).symm).val.app U
        ((eqToHom (S.model.obj_eq M)).val.app U
          ((S.ordinaryAdjunction.unit.app M).val.app U x)) := (hi _).symm
    _ = (eqToHom (S.model.obj_eq M).symm).val.app U (extensionUnit φ M U x) :=
      congrArg _ hs
    _ = _ := hc.symm

private theorem unit_model_flat (S : ScalarData.{c, v, r} φ)
    (P : CochainComplex (Mod.{c, v, r} J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    S.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
      (res φ).mapDerivedCategory.map (S.model.ε.app P) ≫
      (res φ).mapDerivedCategoryFactors.hom.app
        ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have ht := S.transpose_model P ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P)
    hp (𝟙 _)
  rw [DerivedCategory.Q.map_id] at ht
  simp only [Adjunction.homEquiv_unit, resD] at ht
  repeat' first
    | erw [CategoryTheory.Functor.map_id] at ht
    | erw [Category.comp_id] at ht
  simpa only [Category.assoc] using ht

/-- The model-unit equation holds on arbitrary complexes, without flatness.
Source: Stacks 06YY, 07A6, and the representative equation in ScalarData.
(blueprint: lem-sfb-scalar-model-unit).
Proof: the two composites are natural transformations on complexes. They agree
on K-flat complexes by the representative transpose at the identity. Every complex
has a K-flat resolution, whose image under Q is invertible. Naturality and
cancellation of that image give equality on the original complex. -/
theorem ScalarData.unit_model (S : ScalarData.{c, v, r} φ)
    (P₀ : CochainComplex (Mod.{c, v, r} J R) ℤ) :
    S.adjunction.unit.app (DerivedCategory.Q.obj P₀) ≫
      (res φ).mapDerivedCategory.map (S.model.ε.app P₀) ≫
      (res φ).mapDerivedCategoryFactors.hom.app
        ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P₀) =
      DerivedCategory.Q.map
        ((S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P₀) := by
  let EC := S.model.E.mapHomologicalComplex (.up ℤ)
  let GC := (res φ).mapHomologicalComplex (.up ℤ)
  let α : DerivedCategory.Q ⟶ EC ⋙ GC ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q S.adjunction.unit ≫
      Functor.whiskerRight S.model.ε (res φ).mapDerivedCategory ≫
      Functor.whiskerLeft EC (res φ).mapDerivedCategoryFactors.hom
  let β : DerivedCategory.Q ⟶ EC ⋙ GC ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit
      DerivedCategory.Q
  change α.app P₀ = β.app P₀
  obtain ⟨P, f, hp, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
  let : IsIso (DerivedCategory.Q.map f) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
  apply (cancel_epi (DerivedCategory.Q.map f)).mp
  rw [α.naturality, β.naturality]
  have hf : α.app P = β.app P := unit_model_flat S P hp
  rw [hf]

private theorem derived_unit_flat (S : ScalarData.{c, v, r} φ)
    (P : CochainComplex (Mod.{c, v, r} J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    S.adjunction.unit.app (DerivedCategory.Q.obj P) =
      (SheafOfModules.sheafScalarDerivedAdjunction φ S.model).unit.app
        (DerivedCategory.Q.obj P) := by
  have ht := unit_model_flat S P hp
  have hc := SheafOfModules.scalar_derived_unit φ S.model P hp
  have hu := ordinary_unit_eq S
  have ha : S.ordinaryAdjunction =
      SheafOfModules.sheafScalarOrdinaryAdjunction φ S.model := Adjunction.ext hu
  have hm : (S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit =
      ((SheafOfModules.sheafScalarOrdinaryAdjunction φ S.model).mapHomologicalComplex
        (.up ℤ)).unit := by rw [ha]
  have : IsIso (S.model.ε.app P) := S.model.computes P hp
  apply (cancel_mono ((res φ).mapDerivedCategory.map (S.model.ε.app P) ≫
    (res φ).mapDerivedCategoryFactors.hom.app
      ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P))).1
  rw [hc, ← hm]
  exact ht

private theorem derived_unit_eq (S : ScalarData.{c, v, r} φ) :
    S.adjunction.unit = (SheafOfModules.sheafScalarDerivedAdjunction φ S.model).unit := by
  ext K
  let P₀ := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨P, f, hp, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
  let : IsIso (DerivedCategory.Q.map f) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
  let e' := asIso (DerivedCategory.Q.map f) ≪≫ e
  apply (cancel_epi e'.hom).mp
  calc
    _ = S.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (S.model.T ⋙ (res φ).mapDerivedCategory).map e'.hom := by
      simpa only [Functor.id_map] using S.adjunction.unit.naturality e'.hom
    _ = _ := by rw [derived_unit_flat S P hp]
    _ = _ := by
      simpa only [Functor.id_map] using
        ((SheafOfModules.sheafScalarDerivedAdjunction φ S.model).unit.naturality e'.hom).symm
/-- The specified scalar adjunction is the normalized canonical adjunction.
Source: Stacks 06YY and 07A6 (blueprint: lem-sfb-scalar-adjunction-unique).
Proof: the section equation identifies the ordinary units. At a K-flat complex,
transpose_model at the identity identifies the derived units, since the counit
comparison is invertible there. A K-flat resolution and naturality extend this
equality to every complex, then essential surjectivity to every derived object.
An adjunction is determined by its unit. -/
theorem ScalarData.adjunction_eq (S : ScalarData.{c, v, r} φ) :
    S.adjunction = SheafOfModules.sheafScalarDerivedAdjunction φ S.model :=
  Adjunction.ext (derived_unit_eq S)
end WeilConjectures.SemilinearSections
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
