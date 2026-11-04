/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorPresentation
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.Functor.CurryComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMateIsIso

/-!
# Compatibility of derived tensor comparisons normalized on K-flat representatives

Let `F : C₁ ⥤ C₂`, `F' : D₁ ⥤ D₂`, `N₁ : C₁ ⥤ D₁` and `N₂ : C₂ ⥤ D₂` be exact functors of abelian
categories with an isomorphism `a : N₁ ⋙ F' ≅ F ⋙ N₂`, and suppose that the four categories carry
total tensor products of complexes and derived tensor products, related on "flat" complexes by
model isomorphisms. Let `φ`, `m₁`, `m₂` be the derived comparisons of `F`, `N₁`, `N₂` with the
derived tensor products, each normalized on flat representatives by a totalized comparison
(`CategoryTheory.OpenTensorRestrictionNormalization`), and let `φ'` be a comparison for a functor
`F'' ≅ D(F')`, normalized in the same way.

If the totalized comparisons are compatible with `a` on complexes and every object of `D(C₁)` is
isomorphic to a flat complex, then the derived comparisons satisfy
`CategoryTheory.Adjunction.ComparisonCompatible` for the isomorphism
`D(N₁) ⋙ F'' ≅ D(F) ⋙ D(N₂)` induced by `a`
(`CategoryTheory.comparisonCompatible_of_totalComparison`).
-/

@[expose] public section

universe a b

open CategoryTheory Limits

namespace CategoryTheory

/-- The isomorphism `N₁ ⋙ F' ≅ F ⋙ N₂` of additive functors, applied termwise to complexes:
`F' (N₁ X) ≅ N₂ (F X)`. -/
noncomputable def Functor.mapHomologicalComplexSquareIso {C₁ C₂ D₁ D₂ : Type*} [Category* C₁]
    [Category* C₂] [Category* D₁] [Category* D₂] [Preadditive C₁] [Preadditive C₂]
    [Preadditive D₁] [Preadditive D₂] {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂} {N₁ : C₁ ⥤ D₁} {N₂ : C₂ ⥤ D₂}
    [F.Additive] [F'.Additive] [N₁.Additive] [N₂.Additive] (a : N₁ ⋙ F' ≅ F ⋙ N₂) {ι : Type*}
    (c : ComplexShape ι) :
    N₁.mapHomologicalComplex c ⋙ F'.mapHomologicalComplex c ≅
      F.mapHomologicalComplex c ⋙ N₂.mapHomologicalComplex c :=
  Functor.mapHomologicalComplexCompIso a c ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ N₂)) c).symm

/-- Two natural transformations of bifunctors agree if they agree on all pairs of objects from
two classes meeting every isomorphism class. -/
lemma NatTrans.ext₂_of_exists_iso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {B₁ B₂ : C ⥤ D ⥤ E} (η η' : B₁ ⟶ B₂) (p : C → Prop) (q : D → Prop)
    (hp : ∀ x, ∃ x', p x' ∧ Nonempty (x ≅ x')) (hq : ∀ y, ∃ y', q y' ∧ Nonempty (y ≅ y'))
    (h : ∀ x y, p x → q y → (η.app x).app y = (η'.app x).app y) : η = η' := by
  ext x y
  obtain ⟨x', hx', ⟨i⟩⟩ := hp x
  obtain ⟨y', hy', ⟨j⟩⟩ := hq y
  have e (θ : B₁ ⟶ B₂) : (θ.app x).app y ≫ (B₂.map i.hom).app y ≫ (B₂.obj x').map j.hom =
      (B₁.map i.hom).app y ≫ (B₁.obj x').map j.hom ≫ (θ.app x').app y' := by
    rw [← NatTrans.comp_app_assoc, ← θ.naturality, NatTrans.comp_app_assoc,
      (θ.app x').naturality]
  rw [← cancel_mono ((B₂.map i.hom).app y ≫ (B₂.obj x').map j.hom), e, e, h x' y' hx' hy']



variable {C₁ C₂ D₁ D₂ : Type a} [Category.{b} C₁] [Category.{b} C₂] [Category.{b} D₁]
  [Category.{b} D₂] [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory.{b} C₁] [HasDerivedCategory.{b} C₂] [HasDerivedCategory.{b} D₁]
  [HasDerivedCategory.{b} D₂]
  {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {F' : D₁ ⥤ D₂} [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  {N₁ : C₁ ⥤ D₁} [N₁.Additive] [PreservesFiniteLimits N₁] [PreservesFiniteColimits N₁]
  {N₂ : C₂ ⥤ D₂} [N₂.Additive] [PreservesFiniteLimits N₂] [PreservesFiniteColimits N₂]
  (a : N₁ ⋙ F' ≅ F ⋙ N₂)
  {F'' : DerivedCategory D₁ ⥤ DerivedCategory D₂} (e : F'' ≅ F'.mapDerivedCategory)
  {TC₁ : CochainComplex C₁ ℤ ⥤ CochainComplex C₁ ℤ ⥤ CochainComplex C₁ ℤ}
  {TC₂ : CochainComplex C₂ ℤ ⥤ CochainComplex C₂ ℤ ⥤ CochainComplex C₂ ℤ}
  {TD₁ : CochainComplex D₁ ℤ ⥤ CochainComplex D₁ ℤ ⥤ CochainComplex D₁ ℤ}
  {TD₂ : CochainComplex D₂ ℤ ⥤ CochainComplex D₂ ℤ ⥤ CochainComplex D₂ ℤ}
  {DC₁ : DerivedCategory C₁ × DerivedCategory C₁ ⥤ DerivedCategory C₁}
  {DC₂ : DerivedCategory C₂ × DerivedCategory C₂ ⥤ DerivedCategory C₂}
  {DD₁ : DerivedCategory D₁ ⥤ DerivedCategory D₁ ⥤ DerivedCategory D₁}
  {DD₂ : DerivedCategory D₂ ⥤ DerivedCategory D₂ ⥤ DerivedCategory D₂}
  {fC₁ : CochainComplex C₁ ℤ → Prop} {fC₂ : CochainComplex C₂ ℤ → Prop}
  {fD₁ : CochainComplex D₁ ℤ → Prop} {fD₂ : CochainComplex D₂ ℤ → Prop}
  {hF : ∀ T, fC₁ T → fC₂ ((F.mapHomologicalComplex (.up ℤ)).obj T)}
  {hN₁ : ∀ T, fC₁ T → fD₁ ((N₁.mapHomologicalComplex (.up ℤ)).obj T)}
  {hN₂ : ∀ T, fC₂ T → fD₂ ((N₂.mapHomologicalComplex (.up ℤ)).obj T)}
  (hF' : ∀ T, fD₁ T → fD₂ ((F'.mapHomologicalComplex (.up ℤ)).obj T))
  {mC₁ : ∀ P T, fC₁ P → fC₁ T → (DC₁.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅ DerivedCategory.Q.obj ((TC₁.obj P).obj T))}
  {mC₂ : ∀ P T, fC₂ P → fC₂ T → (DC₂.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅ DerivedCategory.Q.obj ((TC₂.obj P).obj T))}
  {mD₁ : ∀ P T, fD₁ P → fD₁ T →
    ((Functor.uncurry.obj DD₁).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅ DerivedCategory.Q.obj ((TD₁.obj P).obj T))}
  {mD₂ : ∀ P T, fD₂ P → fD₂ T →
    ((Functor.uncurry.obj DD₂).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅ DerivedCategory.Q.obj ((TD₂.obj P).obj T))}
  {tF : ∀ P T, (F.mapHomologicalComplex (.up ℤ)).obj ((TC₁.obj P).obj T) ≅
    (TC₂.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj T)}
  {tN₁ : ∀ P T, (N₁.mapHomologicalComplex (.up ℤ)).obj ((TC₁.obj P).obj T) ≅
    (TD₁.obj ((N₁.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((N₁.mapHomologicalComplex (.up ℤ)).obj T)}
  {tN₂ : ∀ P T, (N₂.mapHomologicalComplex (.up ℤ)).obj ((TC₂.obj P).obj T) ≅
    (TD₂.obj ((N₂.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((N₂.mapHomologicalComplex (.up ℤ)).obj T)}
  (tF' : ∀ P T, (F'.mapHomologicalComplex (.up ℤ)).obj ((TD₁.obj P).obj T) ⟶
    (TD₂.obj ((F'.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((F'.mapHomologicalComplex (.up ℤ)).obj T))
  {φ : DC₁ ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory.prod F.mapDerivedCategory ⋙ DC₂}
  {m₁ : DC₁ ⋙ N₁.mapDerivedCategory ≅
    N₁.mapDerivedCategory.prod N₁.mapDerivedCategory ⋙ Functor.uncurry.obj DD₁}
  {m₂ : DC₂ ⋙ N₂.mapDerivedCategory ≅
    N₂.mapDerivedCategory.prod N₂.mapDerivedCategory ⋙ Functor.uncurry.obj DD₂}
  (φ' : (Functor.postcompose₂.obj F'').obj DD₁ ⟶
    (((Functor.whiskeringLeft₂ _).obj F'').obj F'').obj DD₂)

/-- The normalization of a comparison `φ' : F'' (K ⊗ L) ⟶ F'' K ⊗ F'' L` on flat
representatives `P`, `T`: through `e : F'' ≅ D(F')` and the models, it is the localization of the
totalized comparison `tF'`. -/
def ComparisonNormalization : Prop :=
  ∀ P T (hP : fD₁ P) (hT : fD₁ T),
    (φ'.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj T) ≫
        (Functor.uncurry.obj DD₂).map
          (Prod.mkHom (e.hom.app _ ≫ F'.mapDerivedCategoryFactors.hom.app P)
            (e.hom.app _ ≫ F'.mapDerivedCategoryFactors.hom.app T)) ≫
        (mD₂ _ _ (hF' P hP) (hF' T hT)).hom =
      F''.map (mD₁ P T hP hT).hom ≫ e.hom.app _ ≫ F'.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map (tF' P T)


private lemma uncurry_map_mkHom_comp {D : Type*} [Category* D] (DD : D ⥤ D ⥤ D)
    ⦃X₁ X₂ X₃ Y₁ Y₂ Y₃ : D⦄
    (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃) (g : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) :
    (Functor.uncurry.obj DD).map (Prod.mkHom (f ≫ f') (g ≫ g')) =
      (Functor.uncurry.obj DD).map (Prod.mkHom f g) ≫
        (Functor.uncurry.obj DD).map (Prod.mkHom f' g') := by
  rw [← Functor.map_comp]
  rfl

/-- Naturality of a comparison `φ' : F'' (x ⊗ y) ⟶ F'' x ⊗ F'' y` in both variables. -/
private lemma app_app_comp_uncurry_map_mkHom {D D' : Type*} [Category* D] [Category* D']
    {F'' : D ⥤ D'} {DD₁ : D ⥤ D ⥤ D} {DD₂ : D' ⥤ D' ⥤ D'}
    (φ' : (Functor.postcompose₂.obj F'').obj DD₁ ⟶
      (((Functor.whiskeringLeft₂ _).obj F'').obj F'').obj DD₂)
    ⦃x x' y y' : D⦄ ⦃Z : D'⦄ (f : x ⟶ x') (g : y ⟶ y') (h : _ ⟶ Z) :
    (φ'.app x).app y ≫ (Functor.uncurry.obj DD₂).map (Prod.mkHom (F''.map f) (F''.map g)) ≫ h =
      F''.map ((Functor.uncurry.obj DD₁).map (Prod.mkHom f g)) ≫ (φ'.app x').app y' ≫ h := by
  have h₁ := NatTrans.congr_app (φ'.naturality f) y
  have h₂ := (φ'.app x').naturality g
  dsimp at h₁ h₂
  change (φ'.app x).app y ≫ ((DD₂.map (F''.map f)).app (F''.obj y) ≫
      (DD₂.obj (F''.obj x')).map (F''.map g)) ≫ h =
    F''.map ((DD₁.map f).app y ≫ (DD₁.obj x').map g) ≫ (φ'.app x').app y' ≫ h
  simp only [Category.assoc]
  rw [← reassoc_of% h₁, ← reassoc_of% h₂, F''.map_comp, Category.assoc]

include hF hN₁ hN₂ in
/-- The flat case of `CategoryTheory.comparisonCompatible_of_totalComparison`. -/
lemma comparisonCompatible_app_of_totalComparison
    (hmD₂ : ∀ P P' T T' (hP : fD₂ P) (hP' : fD₂ P') (hT : fD₂ T) (hT' : fD₂ T')
      (f : P ⟶ P') (g : T ⟶ T'),
      (Functor.uncurry.obj DD₂).map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫ (mD₂ P' T' hP' hT').hom =
        (mD₂ P T hP hT).hom ≫ DerivedCategory.Q.map ((TD₂.map f).app T ≫ (TD₂.obj P').map g))
    (hφ : OpenTensorRestrictionNormalization F TC₂ TC₁ DC₂ DC₁ fC₂ fC₁ hF mC₂ mC₁ tF φ)
    (hm₁ : OpenTensorRestrictionNormalization N₁ TD₁ TC₁ (Functor.uncurry.obj DD₁) DC₁ fD₁ fC₁
      hN₁ mD₁ mC₁ tN₁ m₁)
    (hm₂ : OpenTensorRestrictionNormalization N₂ TD₂ TC₂ (Functor.uncurry.obj DD₂) DC₂ fD₂ fC₂
      hN₂ mD₂ mC₂ tN₂ m₂)
    (hφ' : ComparisonNormalization (mD₁ := mD₁) (mD₂ := mD₂) e hF' tF' φ')
    (P T : CochainComplex C₁ ℤ) (hP : fC₁ P) (hT : fC₁ T)
    (H : (N₂.mapHomologicalComplex (.up ℤ)).map (tF P T).hom ≫ (tN₂ _ _).hom =
      (Functor.mapHomologicalComplexSquareIso a (.up ℤ)).inv.app _ ≫
        (F'.mapHomologicalComplex (.up ℤ)).map (tN₁ P T).hom ≫ tF' _ _ ≫
        (TD₂.map ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app P)).app _ ≫
        (TD₂.obj _).map ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app T)) :
    N₂.mapDerivedCategory.map (φ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        m₂.hom.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P), F.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) =
      (Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
          Functor.mapDerivedCategorySquareIso a).inv.app (DC₁.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        F''.map (m₁.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        (φ'.app (N₁.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).app
          (N₁.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) ≫
        (Functor.uncurry.obj DD₂).map (Prod.mkHom
          ((Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
            Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Q.obj P))
          ((Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
            Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Q.obj T))) := by
  have hmk := uncurry_map_mkHom_comp DD₂
  -- `α` on `Q X`, through the factorizations.
  have hα (X : CochainComplex C₁ ℤ) :
      (Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
          Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Q.obj X) ≫
          N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
          N₂.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) =
        F''.map (N₁.mapDerivedCategoryFactors.hom.app X) ≫ e.hom.app _ ≫
          F'.mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app X) := by
    have h := Functor.mapDerivedCategorySquareIso_hom_app_Q_obj a X
    have e₁ : (Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
        Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Q.obj X) =
          e.hom.app _ ≫ (Functor.mapDerivedCategorySquareIso a).hom.app
            (DerivedCategory.Q.obj X) := rfl
    rw [e₁, Category.assoc, h, ← e.hom.naturality_assoc]
    rfl
  have hαinv (X : CochainComplex C₁ ℤ) :
      (Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
          Functor.mapDerivedCategorySquareIso a).inv.app (DerivedCategory.Q.obj X) ≫
          F''.map (N₁.mapDerivedCategoryFactors.hom.app X) ≫ e.hom.app _ ≫
          F'.mapDerivedCategoryFactors.hom.app _ =
        N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
          N₂.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).inv.app X) := by
    rw [← cancel_epi ((Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
      Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Q.obj X)),
      Iso.hom_inv_id_app_assoc, reassoc_of% (hα X)]
    simp [← Functor.map_comp]
  have hφ'nat := app_app_comp_uncurry_map_mkHom φ'
  have k₁ := hφ P T hP hT
  have k₂ := hm₂ _ _ (hF P hP) (hF T hT)
  have k₃ := hm₁ P T hP hT
  have k₄ := hφ' _ _ (hN₁ P hP) (hN₁ T hT)
  have k₆ := hmD₂ _ _ _ _ (hF' _ (hN₁ P hP)) (hN₂ _ (hF P hP)) (hF' _ (hN₁ T hT))
    (hN₂ _ (hF T hT)) ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app P)
    ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app T)
  have k₂' : m₂.hom.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
        F.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) ≫
      (Functor.uncurry.obj DD₂).map (Prod.mkHom
        (N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P))
        (N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app T))) =
      N₂.mapDerivedCategory.map (DC₂.map (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
        (F.mapDerivedCategoryFactors.hom.app T))) ≫ m₂.hom.app _ :=
    (m₂.hom.naturality (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
      (F.mapDerivedCategoryFactors.hom.app T))).symm
  have k₇ : (Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
        Functor.mapDerivedCategorySquareIso a).inv.app
          (DC₁.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        F''.map (N₁.mapDerivedCategory.map (mC₁ P T hP hT).hom) =
      N₂.mapDerivedCategory.map (F.mapDerivedCategory.map (mC₁ P T hP hT).hom) ≫
        (Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
          Functor.mapDerivedCategorySquareIso a).inv.app _ :=
    ((Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
      Functor.mapDerivedCategorySquareIso a).inv.naturality (mC₁ P T hP hT).hom).symm
  have kH := congrArg DerivedCategory.Q.map H
  simp only [Functor.map_comp] at kH
  simp only [hmk, Category.assoc] at k₄
  have hR₁ : (Functor.uncurry.obj DD₂).map (Prod.mkHom
        ((Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
          Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Q.obj P))
        ((Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫
          Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Q.obj T))) ≫
      (Functor.uncurry.obj DD₂).map (Prod.mkHom
        (N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          N₂.mapDerivedCategoryFactors.hom.app _)
        (N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app T) ≫
          N₂.mapDerivedCategoryFactors.hom.app _)) ≫
      (mD₂ _ _ (hN₂ _ (hF P hP)) (hN₂ _ (hF T hT))).hom =
      (Functor.uncurry.obj DD₂).map (Prod.mkHom
        (F''.map (N₁.mapDerivedCategoryFactors.hom.app P))
        (F''.map (N₁.mapDerivedCategoryFactors.hom.app T))) ≫
      (Functor.uncurry.obj DD₂).map (Prod.mkHom (e.hom.app _) (e.hom.app _)) ≫
      (Functor.uncurry.obj DD₂).map (Prod.mkHom
        (F'.mapDerivedCategoryFactors.hom.app _) (F'.mapDerivedCategoryFactors.hom.app _)) ≫
      (mD₂ _ _ (hF' _ (hN₁ P hP)) (hF' _ (hN₁ T hT))).hom ≫
      DerivedCategory.Q.map
        ((TD₂.map ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app P)).app _ ≫
          (TD₂.obj _).map ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app T)) := by
    rw [← Category.assoc, ← hmk, hα, hα]
    simp only [hmk, Category.assoc]
    rw [k₆]
    rfl
  -- The isomorphism `v` used to compare both sides.
  have hv : IsIso ((Functor.uncurry.obj DD₂).map (Prod.mkHom
      (N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        N₂.mapDerivedCategoryFactors.hom.app _)
      (N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app T) ≫
        N₂.mapDerivedCategoryFactors.hom.app _)) ≫
      (mD₂ _ _ (hN₂ _ (hF P hP)) (hN₂ _ (hF T hT))).hom) := by
    change IsIso (((DD₂.map _).app _ ≫ (DD₂.obj _).map _) ≫ _)
    infer_instance
  rw [← cancel_mono ((Functor.uncurry.obj DD₂).map (Prod.mkHom
      (N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        N₂.mapDerivedCategoryFactors.hom.app _)
      (N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app T) ≫
        N₂.mapDerivedCategoryFactors.hom.app _)) ≫
      (mD₂ _ _ (hN₂ _ (hF P hP)) (hN₂ _ (hF T hT))).hom)]
  trans N₂.mapDerivedCategory.map (F.mapDerivedCategory.map (mC₁ P T hP hT).hom) ≫
    N₂.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app _) ≫
    N₂.mapDerivedCategoryFactors.hom.app _ ≫
    DerivedCategory.Q.map ((N₂.mapHomologicalComplex (.up ℤ)).map (tF P T).hom) ≫
    DerivedCategory.Q.map (tN₂ _ _).hom
  · rw [hmk]
    simp only [Category.assoc]
    rw [reassoc_of% k₂', k₂]
    simp only [← Functor.map_comp_assoc]
    rw [k₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  · simp only [Category.assoc]
    rw [hR₁, hφ'nat]
    erw [reassoc_of% k₄]
    rw [ ← F''.map_comp_assoc, ← F''.map_comp_assoc]
    simp only [Category.assoc]
    rw [k₃]
    simp only [Functor.map_comp, Category.assoc]
    rw [e.hom.naturality_assoc, Functor.mapDerivedCategoryFactors_hom_naturality_assoc,
      reassoc_of% k₇]
    erw [reassoc_of% (hαinv _)]
    rw [kH]

include hF hN₁ hN₂ in
/-- **Compatibility of derived tensor comparisons normalized on flat representatives.** Let
`a : N₁ ⋙ F' ≅ F ⋙ N₂` be an isomorphism of exact functors, `φ`, `m₁`, `m₂` derived comparisons
of `F`, `N₁`, `N₂` with derived tensor products and `φ'` one of a functor `F'' ≅ D(F')`, all
normalized on flat representatives by totalized comparisons `tF`, `tN₁`, `tN₂`, `tF'`. If the
totalized comparisons are compatible with `a` on flat complexes (`H`) and every object of
`D(C₁)` is isomorphic to a flat complex, then the derived comparisons are compatible with the
isomorphism `D(N₁) ⋙ F'' ≅ D(F) ⋙ D(N₂)` induced by `a`. -/
theorem comparisonCompatible_of_totalComparison
    (hmD₂ : ∀ P P' T T' (hP : fD₂ P) (hP' : fD₂ P') (hT : fD₂ T) (hT' : fD₂ T')
      (f : P ⟶ P') (g : T ⟶ T'),
      (Functor.uncurry.obj DD₂).map (Prod.mkHom (DerivedCategory.Q.map f)
        (DerivedCategory.Q.map g)) ≫ (mD₂ P' T' hP' hT').hom =
        (mD₂ P T hP hT).hom ≫ DerivedCategory.Q.map ((TD₂.map f).app T ≫ (TD₂.obj P').map g))
    (hφ : OpenTensorRestrictionNormalization F TC₂ TC₁ DC₂ DC₁ fC₂ fC₁ hF mC₂ mC₁ tF φ)
    (hm₁ : OpenTensorRestrictionNormalization N₁ TD₁ TC₁ (Functor.uncurry.obj DD₁) DC₁ fD₁ fC₁
      hN₁ mD₁ mC₁ tN₁ m₁)
    (hm₂ : OpenTensorRestrictionNormalization N₂ TD₂ TC₂ (Functor.uncurry.obj DD₂) DC₂ fD₂ fC₂
      hN₂ mD₂ mC₂ tN₂ m₂)
    (hφ' : ComparisonNormalization (mD₁ := mD₁) (mD₂ := mD₂) e hF' tF' φ')
    (H : ∀ P T, fC₁ P → fC₁ T →
      (N₂.mapHomologicalComplex (.up ℤ)).map (tF P T).hom ≫ (tN₂ _ _).hom =
        (Functor.mapHomologicalComplexSquareIso a (.up ℤ)).inv.app _ ≫
          (F'.mapHomologicalComplex (.up ℤ)).map (tN₁ P T).hom ≫ tF' _ _ ≫
          (TD₂.map ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app P)).app _ ≫
          (TD₂.obj _).map ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app T))
    (hess : ∀ x : DerivedCategory C₁, ∃ P, fC₁ P ∧ Nonempty (x ≅ DerivedCategory.Q.obj P)) :
    Adjunction.ComparisonCompatible
      (Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫ Functor.mapDerivedCategorySquareIso a)
      (Functor.curryCompIsoOfIso φ).hom φ' (Functor.curryCompIsoOfIso' m₂)
      (Functor.curryCompIsoOfIso' m₁) := by
  intro x y
  obtain ⟨P, hP, ⟨i⟩⟩ := hess x
  obtain ⟨T, hT, ⟨j⟩⟩ := hess y
  have hflat := comparisonCompatible_app_of_totalComparison a e hF' tF' φ' hmD₂ hφ hm₁ hm₂ hφ' P T hP
    hT (H P T hP hT)
  have hmk := uncurry_map_mkHom_comp DD₂
  have hφ'nat := app_app_comp_uncurry_map_mkHom φ'
  let α := Functor.isoWhiskerLeft N₁.mapDerivedCategory e ≪≫ Functor.mapDerivedCategorySquareIso a
  -- The comparison maps on `(x, y)` and on `(Q P, Q T)` differ by `i` and `j`.
  have hT : IsIso ((Functor.uncurry.obj DD₂).map (Prod.mkHom
      (N₂.mapDerivedCategory.map (F.mapDerivedCategory.map i.hom))
      (N₂.mapDerivedCategory.map (F.mapDerivedCategory.map j.hom)))) := by
    change IsIso ((DD₂.map _).app _ ≫ (DD₂.obj _).map _)
    infer_instance
  rw [← cancel_mono ((Functor.uncurry.obj DD₂).map (Prod.mkHom
      (N₂.mapDerivedCategory.map (F.mapDerivedCategory.map i.hom))
      (N₂.mapDerivedCategory.map (F.mapDerivedCategory.map j.hom))))]
  have hL : N₂.mapDerivedCategory.map (φ.hom.app (x, y)) ≫
      m₂.hom.app (F.mapDerivedCategory.obj x, F.mapDerivedCategory.obj y) ≫
      (Functor.uncurry.obj DD₂).map (Prod.mkHom
        (N₂.mapDerivedCategory.map (F.mapDerivedCategory.map i.hom))
        (N₂.mapDerivedCategory.map (F.mapDerivedCategory.map j.hom))) =
      N₂.mapDerivedCategory.map (F.mapDerivedCategory.map (DC₁.map (Prod.mkHom i.hom j.hom))) ≫
        N₂.mapDerivedCategory.map (φ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        m₂.hom.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
          F.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) := by
    have h₁ := (m₂.hom.naturality (Prod.mkHom (F.mapDerivedCategory.map i.hom)
      (F.mapDerivedCategory.map j.hom))).symm
    have h₂ := φ.hom.naturality (Prod.mkHom i.hom j.hom)
    dsimp at h₁ h₂
    erw [h₁, ← Functor.map_comp_assoc, ← h₂, Functor.map_comp_assoc]
  have hR : α.inv.app (DC₁.obj (x, y)) ≫ F''.map (m₁.hom.app (x, y)) ≫
      (φ'.app (N₁.mapDerivedCategory.obj x)).app (N₁.mapDerivedCategory.obj y) ≫
      (DD₂.map (α.hom.app x)).app _ ≫ (DD₂.obj _).map (α.hom.app y) ≫
      (Functor.uncurry.obj DD₂).map (Prod.mkHom
        (N₂.mapDerivedCategory.map (F.mapDerivedCategory.map i.hom))
        (N₂.mapDerivedCategory.map (F.mapDerivedCategory.map j.hom))) =
      N₂.mapDerivedCategory.map (F.mapDerivedCategory.map (DC₁.map (Prod.mkHom i.hom j.hom))) ≫
        α.inv.app (DC₁.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        F''.map (m₁.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        (φ'.app (N₁.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).app
          (N₁.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) ≫
        (Functor.uncurry.obj DD₂).map (Prod.mkHom (α.hom.app (DerivedCategory.Q.obj P))
          (α.hom.app (DerivedCategory.Q.obj T))) := by
    rw [← Category.assoc ((DD₂.map (α.hom.app x)).app _)]
    change _ ≫ _ ≫ _ ≫ (Functor.uncurry.obj DD₂).map (Prod.mkHom (α.hom.app x) (α.hom.app y)) ≫ _ = _
    have hαi := α.hom.naturality i.hom
    have hαj := α.hom.naturality j.hom
    dsimp at hαi hαj
    rw [← hmk, ← hαi, ← hαj, hmk, hφ'nat]
    have h₁ := m₁.hom.naturality (Prod.mkHom i.hom j.hom)
    have h₂ := α.inv.naturality (DC₁.map (Prod.mkHom i.hom j.hom))
    dsimp at h₁ h₂
    erw [← F''.map_comp_assoc, ← h₁, F''.map_comp_assoc, reassoc_of% h₂]
  simp only [Category.assoc]
  refine hL.trans ?_
  rw [hflat]
  exact hR.symm

end CategoryTheory
