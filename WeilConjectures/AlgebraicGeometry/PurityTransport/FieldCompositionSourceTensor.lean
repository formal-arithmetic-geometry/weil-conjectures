/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceGeometricData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

/-! # Tensor compatibility for the geometric scalar pullback comparison

Source: scalar-six pullback, composition and balanced tensor normalization.
(blueprint: lem-pur-field-composition-source-tensor). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open CategoryTheory.Functor.OplaxMonoidal
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace CategoryTheory
private theorem monoidal_eq_of_delta
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) (m n : F.Monoidal)
    (hd : ∀ X Y, m.toOplaxMonoidal.δ X Y = n.toOplaxMonoidal.δ X Y) : m = n := by
  apply Functor.Monoidal.toOplaxMonoidal_injective
  apply Functor.OplaxMonoidal.ext
  · let := n
    let e : tensorRight (F.obj (𝟙_ A)) ≅ 𝟭 B :=
      (tensoringRight B).mapIso (Functor.Monoidal.εIso F).symm ≪≫ rightUnitorNatIso B
    let : (tensorRight (F.obj (𝟙_ A))).Faithful := Functor.Faithful.of_iso e.symm
    apply (tensorRight (F.obj (𝟙_ A))).map_injective
    change m.toOplaxMonoidal.η ▷ F.obj (𝟙_ A) = n.toOplaxMonoidal.η ▷ F.obj (𝟙_ A)
    have hm := m.toOplaxMonoidal.oplax_left_unitality (𝟙_ A)
    have hn := n.toOplaxMonoidal.oplax_left_unitality (𝟙_ A)
    rw [hd] at hm
    apply (cancel_epi (F.map (λ_ (𝟙_ A)).inv ≫
      n.toOplaxMonoidal.δ (𝟙_ A) (𝟙_ A))).mp
    simpa only [Category.assoc] using hm.symm.trans hn
  · exact funext fun X ↦ funext fun Y ↦ hd X Y
end CategoryTheory
namespace CategoryTheory.Mod
universe v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (CategoryTheory.MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (CategoryTheory.MonoidalCategory.tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
private theorem canonical_normalized (M N : Mod C R) :
    let := extendScalarsMonoidal φ
    tensorObjπ M N ≫ (extendUnit φ (M ⊗ N)).hom ≫
      (Functor.OplaxMonoidal.δ (extendScalars φ) M N).hom =
    ((extendUnit φ M).hom ⊗ₘ (extendUnit φ N).hom) ≫
      tensorObjπ ((extendScalars φ).obj M) ((extendScalars φ).obj N) := by
  let := extendScalarsMonoidal φ
  change tensorObjπ M N ≫ extendUnitHom φ (M ⊗ N) ≫
    ((extendScalarsOplaxMonoidal φ).δ M N).hom = _
  rw [extendScalarsOplaxMonoidal_δ, extendUnitHom_extendHom]
  simp only [MonoidalCategory.tensorHom_def, comp_hom', Category.assoc]
  erw [tensorObjπ_whiskerRight_assoc, tensorObjπ_whiskerLeft_assoc,
    tensorObjπ_comapTensorHom_hom]
  rfl
private theorem chosen_delta_eq (M N : Mod C R) :
    ((exists_extendScalarsMonoidal φ).choose.toOplaxMonoidal.δ M N) =
      (extendScalarsMonoidal φ).toOplaxMonoidal.δ M N := by
  apply (extendHomEquiv φ (M ⊗ N) _).injective
  apply hom_ext
  change extendUnitHom φ (M ⊗ N) ≫ _ = extendUnitHom φ (M ⊗ N) ≫ _
  apply (cancel_epi (tensorObjπ M N)).mp
  exact ((exists_extendScalarsMonoidal φ).choose_spec M N).trans
    (canonical_normalized φ M N).symm
private theorem chosen_monoidal_eq :
    (exists_extendScalarsMonoidal φ).choose = extendScalarsMonoidal φ :=
  monoidal_eq_of_delta _ _ _ (chosen_delta_eq φ)
end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.PurityTransport
attribute [local irreducible] DerivedCategory Functor.leftDerivedFunctor
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private instance (R : ScalarSixRing.{u}) : IsCommMonObj R.X := R.comm
private instance {R S : ScalarSixRing.{u}} (a : R ⟶ S) : IsMonHom a.hom.hom :=
  a.hom.isMonHom_hom
set_option maxHeartbeats 1600000 in
-- Elaborating the native derived comparisons requires their full scalar instances.
private theorem flat_pull (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    [∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom T))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fieldCompScalarPull ell a f =
      derivedPullIso (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom f := by
  apply Iso.ext
  let ay := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom Y)
  let ax := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)
  let t := TwoSquare.mk _ _ _ _ (scalarPullbackIso a f).hom
  let E := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) f
  let E' := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c'.obj ell) f
  have hw : (fieldCompScalarPull ell a f).hom =
      ((t.whiskerTop E.hom).whiskerBottom E'.inv).natTrans := by
    ext M
    simp only [fieldCompScalarPull, t, E, E', TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Category.assoc]
  rw [hw]
  apply congrArg TwoSquare.natTrans ((mateEquiv ay ax).injective ?_)
  change mateEquiv ay ax ((t.whiskerTop E.hom).whiskerBottom E'.inv) = _
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_derivedPullIso_hom]
  have ht : mateEquiv ay ax (TwoSquare.mk _ _ _ _ (scalarPullbackIso a f).hom) =
      TwoSquare.mk _ _ _ _
        (derivedComapUpperStarIso (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom f).inv := by
    change (mateEquiv ay ax) ((mateEquiv ay ax).symm _) = _
    exact Equiv.apply_symm_apply _ _
  rw [ht]
  ext M
  simp only [E, E', derivedComapLeftDerivedUpperStarIso,
    derivedComapUpperStarIso, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.mk, Iso.trans_inv, Iso.symm_inv,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.assoc]

set_option maxHeartbeats 1600000 in
-- Elaborating the native derived comparisons requires their full scalar instances.
private theorem monoidal_native (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) (T : Scheme.{u}) :
    fieldCompScalarMonoidal ell a T = scalarSixChangeMonoidal a T := by
  let φ : condensedRingObj (c.obj ell) T ⟶ condensedRingObj (c'.obj ell) T :=
    coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom T
  let κ : (Mod.extendScalars φ).Monoidal → (scalarSixChange a T).Monoidal := fun m ↦ by
    letI := m
    let := Mod.extendScalars_preservesFlat φ
    let := (Mod.extendRestrictAdjunction φ).isLeftAdjoint
    exact (Mod.extendScalars φ).leftDerivedFunctorMonoidal
  exact congrArg κ (CategoryTheory.Mod.chosen_monoidal_eq φ)
set_option maxHeartbeats 1600000 in
-- Elaborating the native derived comparisons requires their full scalar instances.
/-- The literal geometric scalar comparison respects inverse derived tensorators
for a coefficient map whose ordinary extensions are exact on every scheme.
Source: scalar-six tensor normalization and the native flat scalar/pullback
comparison. (blueprint: lem-pur-field-composition-source-tensor).

Proof in words. The balanced tensor pairing and scalar adjunction determine the
chosen ordinary inverse tensorator. The canonical ordinary monoidal structure
satisfies that normalization. Oplax unit coherence, followed by faithfulness of
tensoring with the invertible image of the unit, determines its unit map too.
The monoidal structures therefore agree, and their left-derived structures agree.
Next express fieldCompScalarPull by whiskering its exact scalar mate with the
total-to-exact comparisons. Injectivity of the mate equivalence identifies this
with derivedPullIso: its mate is the same exact comap/pullback square, transported
by those comparisons. Finally apply comparisonCompatible_derivedPullIso. Its
inverse tensorators are definitionally the native derived tensor comparisons.
Postcompose with the tensor of the inverse pullback comparisons and cancel to
obtain the stated equation on arbitrary derived inputs. -/
theorem fieldCompositionSourceTensor (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    [∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom T))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := fieldCompScalarMonoidal ell a X
    letI := fieldCompScalarMonoidal ell a Y
    ∀ N L : c.derived ell Y,
      (fieldCompScalarPull ell a f).hom.app (N ⊗ L) ≫
        (actualPull (c'.obj ell) f).map (δ (scalarSixChange a Y) N L) ≫
        δ (actualPull (c'.obj ell) f)
          ((scalarSixChange a Y).obj N) ((scalarSixChange a Y).obj L) =
      (scalarSixChange a X).map (δ (actualPull (c.obj ell) f) N L) ≫
        δ (scalarSixChange a X) ((actualPull (c.obj ell) f).obj N)
          ((actualPull (c.obj ell) f).obj L) ≫
        ((fieldCompScalarPull ell a f).hom.app N ⊗ₘ
          (fieldCompScalarPull ell a f).hom.app L) := by
  rw [monoidal_native ell a X, monoidal_native ell a Y]
  intro N L
  rw [flat_pull ell a f]
  let (T : Scheme.{u}) :
      (Mod.extendScalars (coefficientMap
        (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom T)).Monoidal :=
    Mod.extendScalarsMonoidal _
  let (T : Scheme.{u}) : (scalarSixChange a T).Monoidal := scalarSixChangeMonoidal a T
  have h := comparisonCompatible_derivedPullIso
    (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom f N L
  have hδ (T : Scheme.{u}) (M P : c.derived ell T) :
      δ (scalarSixChange a T) M P =
        ((Mod.extendScalars (coefficientMap
          (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom T)).leftDerivedTensorComparison.app
            M).app P := rfl
  have hF (M P : c.derived ell Y) : δ (actualPull (c.obj ell) f) M P =
      ((leftDerivedUpperStarTensor (c.obj ell) f).app M).app P := rfl
  have hF' (M P : c'.derived ell Y) : δ (actualPull (c'.obj ell) f) M P =
      ((leftDerivedUpperStarTensor (c'.obj ell) f).app M).app P := rfl
  simp only [hδ, hF, hF']
  apply (cancel_mono
    ((derivedPullIso (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom f).inv.app N ⊗ₘ
      (derivedPullIso (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom f).inv.app L)).mp
  simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id_app]
  simpa only [derivedExtendScalarsTensorIso, asIso_hom, Iso.symm_inv, Iso.symm_hom,
    curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    Functor.comp_obj, Category.assoc, MonoidalCategory.tensorHom_def,
    id_whiskerRight, whiskerLeft_id, Category.comp_id,
    scalarSixChange, scalarSixAdjunctionLeft, actualPull,
    Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringLeft,
    Functor.whiskeringRight, Functor.comp_obj] using h.symm

end AlgebraicGeometry.ProEtale.PurityTransport
