/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.LocalizedOpenSheafification
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverComponentIdentity
import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-! # Normalized tensor summands under the open-site equivalence

## References

* Stacks Project, Tag 0A8X, ordinary tensor totalization.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

open BraidedCategory Functor MonoidalCategory.Functor

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
-- The proof uses the equivalence API, never its large sectionwise implementation.
attribute [local irreducible] Scheme.Modules.overEquiv

attribute [local instance] ordinaryComponentIdentityOverPreadditive

attribute [local instance] ordinaryComponentIdentitySchemePreadditive

section Normalize
universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
private def scalarIso (b : 𝟙_ D ≅ 𝟙_ D) : 𝟭 D ≅ 𝟭 D :=
  NatIso.ofComponents (fun X ↦ (λ_ X).symm ≪≫ whiskerRightIso b X ≪≫ λ_ X)
    (by
      intro X Y f
      dsimp
      simp only [Category.assoc, whiskerRightIso_hom]
      rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
        leftUnitor_naturality])
private theorem scalarIso_unit (b : 𝟙_ D ≅ 𝟙_ D) :
    (scalarIso b).hom.app (𝟙_ D) = b.hom := by
  dsimp [scalarIso]
  rw [whiskerRightIso_hom, unitors_equal, rightUnitor_naturality, unitors_inv_equal,
    Iso.inv_hom_id_assoc]
variable [BraidedCategory C] [BraidedCategory D]

private theorem normalize (F : C ⥤ D) [F.Braided]
    (e : 𝟙_ D ≅ F.obj (𝟙_ C)) :
    ∃ m : F.CoreMonoidal, m.εIso = e ∧
      ∀ A B : C, F.map (β_ A B).hom ≫ (m.μIso B A).inv =
        (m.μIso A B).inv ≫ (β_ (F.obj A) (F.obj B)).hom := by
  let b := e ≪≫ (Functor.Monoidal.εIso F).symm
  let a : F ≅ F := NatIso.ofComponents (fun X ↦ (scalarIso b).app (F.obj X))
    (fun f ↦ (scalarIso b).hom.naturality (F.map f))
  let m := Functor.Monoidal.coreMonoidalTransport a
  refine ⟨m, ?_, ?_⟩
  · apply Iso.ext
    change (Functor.Monoidal.εIso F).hom ≫ a.hom.app (𝟙_ C) = e.hom
    have hn := (scalarIso b).hom.naturality (Functor.Monoidal.εIso F).hom
    dsimp only [Functor.id_map] at hn
    change (Functor.Monoidal.εIso F).hom ≫
      (scalarIso b).hom.app (F.obj (𝟙_ C)) = e.hom
    rw [hn, scalarIso_unit]
    simp [b]
  · intro A B
    simp only [m, Functor.Monoidal.coreMonoidalTransport_μIso_inv, Category.assoc]
    rw [a.inv.naturality_assoc]
    rw [braiding_naturality]
    congr 1
    rw [Functor.map_braiding]
    simp

end Normalize

section Descent
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
private theorem braided_descent (L : C ⥤ D) [L.Braided] (W : MorphismProperty C)
    [L.IsLocalization W] [W.ContainsIdentities]
    (F : D ⥤ E) [F.Monoidal]
    (hbr : ∀ X Y : C,
      (Functor.LaxMonoidal.μ F (L.obj X) (L.obj Y) ≫
        F.map (Functor.LaxMonoidal.μ L X Y)) ≫ F.map (L.map (β_ X Y).hom) =
      (β_ (F.obj (L.obj X)) (F.obj (L.obj Y))).hom ≫
        (Functor.LaxMonoidal.μ F (L.obj Y) (L.obj X) ≫
          F.map (Functor.LaxMonoidal.μ L Y X))) :
    ∀ X Y : D, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X := by
  let t := Functor.curriedTensorPreIsoPost F
  let bp := (postcompose₂.obj F).mapIso (curriedBraidingNatIso D)
  let bi := (((whiskeringLeft₂ E).obj F).obj F).mapIso (curriedBraidingNatIso E)
  let a : curriedTensorPre F ⟶ (curriedTensorPost F).flip := t.hom ≫ bp.hom
  let b : curriedTensorPre F ⟶ (curriedTensorPost F).flip :=
    bi.hom ≫ (flipFunctor _ _ _).map t.hom
  have hab : a = b := by
    apply Localization.natTrans₂_ext L L W W
    intro X Y
    change Functor.LaxMonoidal.μ F (L.obj X) (L.obj Y) ≫
        F.map (β_ (L.obj X) (L.obj Y)).hom =
      (β_ (F.obj (L.obj X)) (F.obj (L.obj Y))).hom ≫
        Functor.LaxMonoidal.μ F (L.obj Y) (L.obj X)
    have h := hbr X Y
    apply (cancel_mono (F.map (Functor.LaxMonoidal.μ L Y X))).1
    simpa only [Category.assoc, ← F.map_comp, Functor.LaxBraided.braided] using h
  intro X Y
  exact congrArg (fun k ↦ (k.app X).app Y) hab

end Descent

set_option maxHeartbeats 500000 in
-- Monoidal localization and its coefficient instances require extra elaboration heartbeats.
/-- The open-site equivalence has a symmetric core monoidal structure with its
prescribed unit (Stacks, Tag 01CD). -/
private theorem exists_normalizedOpen_coreMonoidal (X : Scheme.{u}) (U : X.Opens) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    ∃ m : L.CoreMonoidal,
      m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U ∧
      (∀ A B : localEvaluationModules X U,
        L.map (β_ A B).hom ≫ (m.μIso B A).inv =
          (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom) := by
  let : MonoidalCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.monoidalCategory (X.sheaf.over U)
  let : SymmetricCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.symmetricCategory (X.sheaf.over U)
  let E := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  let : MonoidalCategory
      (PresheafOfModules.{u} ((moduleRings X.toRingedSpace).over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  let : MonoidalCategory
      (PresheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace).obj) :=
    PresheafOfModules.monoidalCategory (R := U.toScheme.sheaf.obj)
  let : SymmetricCategory
      (PresheafOfModules.{u} ((moduleRings X.toRingedSpace).over U).obj) :=
    PresheafOfModules.symmetricCategory (R := (X.sheaf.over U).obj)
  let : SymmetricCategory
      (PresheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace).obj) :=
    PresheafOfModules.symmetricCategory (R := U.toScheme.sheaf.obj)
  let L := PresheafOfModules.sheafification.{u}
    (R := (moduleRings X.toRingedSpace).over U)
    (𝟙 ((moduleRings X.toRingedSpace).over U).obj)
  let P := PresheafOfModules.pushforward₀OfCommRingCat
    (TopologicalSpace.Opens.overEquivalence U).inverse (X.sheaf.over U).obj
  let S := PresheafOfModules.sheafification.{u}
    (R₀ := (moduleRings U.toScheme.toRingedSpace).obj)
    (R := moduleRings U.toScheme.toRingedSpace)
    (𝟙 (moduleRings U.toScheme.toRingedSpace).obj)
  let W := ((Opens.grothendieckTopology X).over U).W.inverseImage
    (PresheafOfModules.toPresheaf.{u} ((moduleRings X.toRingedSpace).over U).obj)
  let : L.Braided := SheafOfModules.sheafificationBraided (X.sheaf.over U)
  let : S.Braided := SheafOfModules.sheafificationBraided U.toScheme.sheaf
  let : P.Braided :=
    { __ := (inferInstance : P.Monoidal)
      braided A B := by
        ext1
        exact ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl }
  let : (P ⋙ S).Braided := inferInstance
  obtain ⟨h⟩ := exists_localizedOpen_sheafification_iso X U
  let : Localization.Lifting L W (P ⋙ S) E := ⟨h⟩
  let : E.Monoidal := Localization.Monoidal.functorMonoidalOfComp L W E (P ⋙ S)
  let : h.hom.IsMonoidal := Localization.Monoidal.lifting_isMonoidal L W E (P ⋙ S)
  have hb := braided_descent L W E (by
    intro A B
    change Functor.LaxMonoidal.μ (L ⋙ E) A B ≫ (L ⋙ E).map (β_ A B).hom =
      (β_ ((L ⋙ E).obj A) ((L ⋙ E).obj B)).hom ≫
        Functor.LaxMonoidal.μ (L ⋙ E) B A
    have hm (A B) := NatTrans.IsMonoidal.tensor (τ := h.hom) A B
    apply (cancel_mono (h.hom.app (B ⊗ A))).1
    simp only [Category.assoc]
    rw [h.hom.naturality, ← Category.assoc, hm A B]
    simp only [Category.assoc]
    rw [hm B A, Functor.LaxBraided.braided, braiding_naturality_assoc])
  let : E.Braided :=
    { toMonoidal := (inferInstance : E.Monoidal)
      braided := hb }
  exact normalize E (Scheme.Modules.overEquivFunctorObjUnitIso U)


set_option maxHeartbeats 700000 in
-- Elaborating two nested bicomplex comparisons requires additional heartbeats.
/-- The open-site tensor comparison has the prescribed unit, symmetry and total summands
(Stacks, Tag 0A8X). -/
theorem exists_ordinaryEvaluation_tensor_summands (X : Scheme.{u}) (U : X.Opens) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∃ m : L.CoreMonoidal,
      m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U ∧
      (∀ A B : localEvaluationModules X U,
        L.map (β_ A B).hom ≫ (m.μIso B A).inv =
          (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom) ∧
      ∀ P F : CochainComplex (localEvaluationModules X U) ℤ,
        ∃ c : T.obj (localEvaluationTensor X U P F) ≅
            pullbackTensorTotal U.toScheme (T.obj F) (T.obj (localEvaluationDual X U P)),
          ∀ (p q n : ℤ) (h : p + q = n),
            L.map (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
                (curriedTensor _) (.up ℤ) p q n h) ≫ c.hom.f n =
              (m.μIso (F.X p) ((localEvaluationDual X U P).X q)).inv ≫
                HomologicalComplex.ιMapBifunctor (T.obj F)
                  (T.obj (localEvaluationDual X U P)) (curriedTensor _) (.up ℤ) p q n h := by
  let R := Equivalence.functor
    (C := localEvaluationModules X U)
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesColimitsOfSize.{0, 0} R := by
    dsimp [R]
    infer_instance
  obtain ⟨m, hm, hs⟩ := exists_normalizedOpen_coreMonoidal X U
  refine ⟨m, hm, hs, ?_⟩
  intro P F
  let K := localEvaluationDual X U P
  let B := (((curriedTensor
    (localEvaluationModules X U)).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj F).obj K
  have : R.PreservesTotalComplex B (.up ℤ) := fun _ ↦ inferInstance
  let e₁ := (HomologicalComplex₂.mapTotalIso R B (.up ℤ)).symm
  let : R.OplaxMonoidal := m.toOplaxMonoidal
  let e₂ :
      (((R.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj B) ≅
        (((curriedTensor (SheafOfModules.{u}
          (moduleRings U.toScheme.toRingedSpace))).mapBifunctorHomologicalComplex
            (.up ℤ) (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj F)).obj
              ((R.mapHomologicalComplex (.up ℤ)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ (m.μIso (F.X p) (K.X q)).symm)
        (by
          intro q q' hq
          change (m.μIso (F.X p) (K.X q)).inv ≫ R.obj (F.X p) ◁ R.map (K.d q q') =
            R.map (F.X p ◁ K.d q q') ≫ (m.μIso (F.X p) (K.X q')).inv
          exact Functor.OplaxMonoidal.δ_natural_right R (F.X p) (K.d q q')))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (m.μIso (F.X p) (K.X q)).inv ≫ R.map (F.d p p') ▷ R.obj (K.X q) =
          R.map (F.d p p' ▷ K.X q) ≫ (m.μIso (F.X p') (K.X q)).inv
        exact Functor.OplaxMonoidal.δ_natural_left R (F.d p p') (K.X q))
  refine ⟨e₁ ≪≫ HomologicalComplex₂.total.mapIso e₂ (.up ℤ), ?_⟩
  intro p q n h
  change R.map (B.ιTotal (.up ℤ) p q n h) ≫
    ((HomologicalComplex₂.mapTotalXIso R B (.up ℤ) n).inv ≫
      (HomologicalComplex₂.total.map e₂.hom (.up ℤ)).f n) = _
  rw [← Category.assoc, HomologicalComplex₂.map_ι_mapTotalXIso_inv]
  rw [HomologicalComplex₂.ιTotal_map]
  rfl

end AlgebraicGeometry
