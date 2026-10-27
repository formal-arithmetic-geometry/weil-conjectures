/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.PbcCommonStageCones
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.CategoryTheory.StageSystem.Functor
import Sheaf.Paper.CommonStageCalculus
import all Sheaf.Paper.FiniteStagePairCategory
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Triangulated.Adjunction
import all Sheaf.Paper.SfFrameworkCommonStageDescent

/-! # Shifts and finite-model reflection for the raw coefficient pairs

Source: main-20261015, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
final sentence, extracted common-stage comparison steps 6--8
(blueprint: lem-fd-shift-triangle-reflection).

The stage morphism uses beta = inverse j. Its existing functor is the prescribed
conjugation on representatives. No Karoubi completion is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w₁ v₁ u₁
open CategoryTheory CategoryTheory.Pretriangulated
namespace FdConeProof
attribute [local irreducible] WeilConjectures.pairShiftIso
  WeilConjectures.pairStageShiftIso
attribute [local instance] StageSystem.pbcPairHasShift
  StageSystem.pbcStageInclusionCommShift
variable {I : Type w₁} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)] (S : StageSystem C)
  [∀ i, HasShift (C i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S.assoc h h').hom ℤ]

private theorem inclusionShift_normalized (i : I) (n : ℤ) (X : C i) :
    ∃ q : (S.ι i).obj (X⟦n⟧) = (shiftFunctor S.PairCategory n).obj ⟨i, X⟩,
      ((S.ι i).commShiftIso n).hom.app X = eqToHom q := by
  exact ⟨rfl, rfl⟩

private theorem inverse_heq {A : Type*} [Category* A]
    {X Y X' Y' : A} (a : X ≅ Y) (b : X' ≅ Y')
    (hX : X = X') (hY : Y = Y') (h : HEq a.hom b.hom) : HEq a.inv b.inv := by
  subst X'
  subst Y'
  have hab : a = b := Iso.ext (eq_of_heq h)
  subst b
  rfl

private theorem preimageIso_comp {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) [F.Full] [F.Faithful] {X Y : A} {Z : B}
    (a : F.obj X ≅ Z) (e : F.obj Y ≅ Z) :
    F.map (F.preimageIso (a ≪≫ e.symm)).hom ≫ e.hom = a.hom := by
  simp

private theorem adjunctionTriangleCounit
    {A B : Type*} [Category* A] [Category* B]
    [HasShift A ℤ] [HasShift B ℤ]
    (F : A ⥤ B) (R : B ⥤ A) [F.CommShift ℤ] [R.CommShift ℤ]
    (adj : F ⊣ R) [hcomm : adj.CommShift ℤ] [IsIso adj.counit] :
    ∀ T : Triangle B, ∃ c : F.mapTriangle.obj (R.mapTriangle.obj T) ≅ T,
      c.hom.hom₁ = adj.counit.app T.obj₁ ∧
      c.hom.hom₂ = adj.counit.app T.obj₂ ∧
      c.hom.hom₃ = adj.counit.app T.obj₃ := by
  let ec : R ⋙ F ≅ 𝟭 B := asIso adj.counit
  have : NatTrans.CommShift ec.hom ℤ := by
    change NatTrans.CommShift adj.counit ℤ
    exact hcomm.commShift_counit
  intro T
  refine ⟨(Functor.mapTriangleCompIso R F).symm.app T ≪≫
    (Functor.mapTriangleIso ec).app T ≪≫
      (Functor.mapTriangleIdIso B).app T, ?_, ?_, ?_⟩
  · change 𝟙 _ ≫ (adj.counit.app T.obj₁ ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
  · change 𝟙 _ ≫ (adj.counit.app T.obj₂ ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
  · change 𝟙 _ ≫ (adj.counit.app T.obj₃ ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]

private theorem finiteInverseTriangle
    {A B : Type*} [Category* A] [Category* B]
    [CategoryTheory.Limits.HasZeroObject A] [CategoryTheory.Limits.HasZeroObject B]
    [Preadditive A] [Preadditive B]
    [HasShift A ℤ] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
    [Pretriangulated A] [Pretriangulated B]
    (F : A ⥤ B) [F.CommShift ℤ] [F.IsEquivalence] [F.IsTriangulated] :
    ∃ (R : B ⥤ A) (adj : F ⊣ R) (r : R.CommShift ℤ),
      (fun [_inverseShift : R.CommShift ℤ] ↦ adj.CommShift ℤ ∧ IsIso adj.unit ∧
        IsIso adj.counit ∧ R.IsTriangulated ∧
        ∀ T : Triangle B, ∃ c : F.mapTriangle.obj (R.mapTriangle.obj T) ≅ T,
          c.hom.hom₁ = adj.counit.app T.obj₁ ∧
          c.hom.hom₂ = adj.counit.app T.obj₂ ∧
          c.hom.hom₃ = adj.counit.app T.obj₃) (_inverseShift := r) := by
  let R := F.inv
  let adj : F ⊣ R := F.asEquivalence.toAdjunction
  let r := adj.rightAdjointCommShift ℤ
  let := r
  have hcomm : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : R.IsTriangulated := adj.isTriangulated_rightAdjoint
  have : IsIso adj.unit := Iso.isIso_hom F.asEquivalence.unitIso
  have : IsIso adj.counit := Iso.isIso_hom F.asEquivalence.counitIso
  exact ⟨R, adj, r, hcomm, inferInstance, inferInstance, inferInstance,
    adjunctionTriangleCounit F R adj⟩

private theorem mapTriangle_of_model
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift D ℤ]
    [CategoryTheory.Limits.HasZeroObject B] [Preadditive B]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    (F : A ⥤ B) [F.CommShift ℤ] (ι : D ⥤ A) [ι.CommShift ℤ]
    (T : Triangle A) (T₀ : Triangle D) (e : T ≅ ι.mapTriangle.obj T₀)
    (h : (ι ⋙ F).mapTriangle.obj T₀ ∈ distTriang B) :
    F.mapTriangle.obj T ∈ distTriang B := by
  exact isomorphic_distinguished _ h _
    (F.mapTriangle.mapIso e ≪≫ (Functor.mapTriangleCompIso ι F).symm.app T₀)

private theorem iso_transport_heq {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {X X' : A} {Y Y' : B} (a : X' ≅ X) (b : Y' ≅ Y)
    (f : F.obj X' ⟶ Y') (p : X = X') (q : Y' = Y)
    (ha : a.inv = eqToHom p) (hb : b.hom = eqToHom q) :
    HEq (F.map a.inv ≫ f ≫ b.hom) f := by
  rw [ha, hb, eqToHom_map]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

section ShiftTransport
universe u₂ v₂
variable {D' : I → Type u₂} [∀ i, Category.{v₂} (D' i)]
  {U : StageSystem C} {V : StageSystem D'}
  [∀ i, HasShift (D' i) ℤ]
  [HasShift U.PairCategory ℤ] [HasShift V.PairCategory ℤ]
  [∀ i, (U.ι i).CommShift ℤ] [∀ i, (V.ι i).CommShift ℤ]
  (F : U.Morphism V) [∀ i, (F.Φ i).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (U.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (V.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (U.transIso h).hom ℤ]
  [∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (V.transIso h).hom ℤ]

private theorem pairShift_normalized
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)
    (n : ℤ) (i : I) (X : C i)
    (p : (shiftFunctor U.PairCategory n).obj ⟨i, X⟩ = (U.ι i).obj (X⟦n⟧))
    (q : (V.ι i).obj (((F.Φ i).obj X)⟦n⟧) =
      (shiftFunctor V.PairCategory n).obj ⟨i, (F.Φ i).obj X⟩)
    (hp : ((U.ι i).commShiftIso n).inv.app X = eqToHom p)
    (hq : ((V.ι i).commShiftIso n).hom.app ((F.Φ i).obj X) = eqToHom q) :
    HEq ((WeilConjectures.pairShiftIso F hβ n).hom.app ⟨i, X⟩)
      ((V.ι i).map (((F.Φ i).commShiftIso n).hom.app X)) ∧
    HEq ((WeilConjectures.pairShiftIso F hβ n).inv.app ⟨i, X⟩)
      ((V.ι i).map (((F.Φ i).commShiftIso n).inv.app X)) := by
  have hh : HEq ((WeilConjectures.pairShiftIso F hβ n).hom.app ⟨i, X⟩)
      ((V.ι i).map (((F.Φ i).commShiftIso n).hom.app X)) := by
    rw [WeilConjectures.pairShiftIso_hom_app]
    exact iso_transport_heq F.functor (((U.ι i).commShiftIso n).app X)
      (((V.ι i).commShiftIso n).app ((F.Φ i).obj X)) _ p q hp hq
  refine ⟨hh, ?_⟩
  exact inverse_heq ((WeilConjectures.pairShiftIso F hβ n).app ⟨i, X⟩)
    ((V.ι i).mapIso (((F.Φ i).commShiftIso n).app X))
    (congrArg F.functor.obj p) q.symm hh

set_option linter.unusedSectionVars false in
private theorem restriction_eq (i : I) : U.ι i ⋙ F.functor = F.Φ i ⋙ V.ι i := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro X Y f
  exact heq_of_eq (F.functor_map_ι f)

private theorem finiteTriangleComparison
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)
    (i : I) (T : Triangle (D' i)) (R : D' i ⥤ C i) [R.CommShift ℤ]
    (c : (F.Φ i).mapTriangle.obj (R.mapTriangle.obj T) ≅ T)
    (ε : R ⋙ F.Φ i ⟶ 𝟭 (D' i))
    (hc₁ : c.hom.hom₁ = ε.app T.obj₁)
    (hc₂ : c.hom.hom₂ = ε.app T.obj₂)
    (hc₃ : c.hom.hom₃ = ε.app T.obj₃) :
    let := WeilConjectures.pairCommShift F hβ
    ∃ e : F.functor.mapTriangle.obj ((U.ι i).mapTriangle.obj (R.mapTriangle.obj T)) ≅
        (V.ι i).mapTriangle.obj T,
      HEq e.hom.hom₁ ((V.ι i).map (ε.app T.obj₁)) ∧
      HEq e.hom.hom₂ ((V.ι i).map (ε.app T.obj₂)) ∧
      HEq e.hom.hom₃ ((V.ι i).map (ε.app T.obj₃)) := by
  let := WeilConjectures.pairCommShift F hβ
  have := WeilConjectures.pairRestrictionShift F hβ i
  let e : F.functor.mapTriangle.obj ((U.ι i).mapTriangle.obj (R.mapTriangle.obj T)) ≅
        (V.ι i).mapTriangle.obj T :=
    (Functor.mapTriangleCompIso _ F.functor).symm.app (R.mapTriangle.obj T) ≪≫
      (Functor.mapTriangleIso (F.ιCompFunctorIso i)).app (R.mapTriangle.obj T) ≪≫
      (Functor.mapTriangleCompIso (F.Φ i) _).app (R.mapTriangle.obj T) ≪≫
      (V.ι i).mapTriangle.mapIso c
  refine ⟨e, ?_, ?_, ?_⟩
  · apply heq_of_eq
    dsimp only [e, Iso.trans, Iso.symm, Iso.app]
    simp only [Functor.mapIso_hom, CategoryTheory.Pretriangulated.comp_hom₁,
      Functor.mapTriangleCompIso_inv_app_hom₁,
      Functor.mapTriangleCompIso_hom_app_hom₁,
      Functor.mapTriangleIso_hom_app_hom₁,
      StageSystem.Morphism.ιCompFunctorIso_hom_app, Functor.mapTriangle_map_hom₁, hc₁]
    erw [Category.id_comp, Category.id_comp, Category.id_comp]
    rfl
  · apply heq_of_eq
    dsimp only [e, Iso.trans, Iso.symm, Iso.app]
    simp only [Functor.mapIso_hom, CategoryTheory.Pretriangulated.comp_hom₂,
      Functor.mapTriangleCompIso_inv_app_hom₂,
      Functor.mapTriangleCompIso_hom_app_hom₂,
      Functor.mapTriangleIso_hom_app_hom₂,
      StageSystem.Morphism.ιCompFunctorIso_hom_app, Functor.mapTriangle_map_hom₂, hc₂]
    erw [Category.id_comp, Category.id_comp, Category.id_comp]
    rfl
  · apply heq_of_eq
    dsimp only [e, Iso.trans, Iso.symm, Iso.app]
    simp only [Functor.mapIso_hom, CategoryTheory.Pretriangulated.comp_hom₃,
      Functor.mapTriangleCompIso_inv_app_hom₃,
      Functor.mapTriangleCompIso_hom_app_hom₃,
      Functor.mapTriangleIso_hom_app_hom₃,
      StageSystem.Morphism.ιCompFunctorIso_hom_app, Functor.mapTriangle_map_hom₃, hc₃]
    erw [Category.id_comp, Category.id_comp, Category.id_comp]
    rfl

section Reflection
variable [∀ i, CategoryTheory.Limits.HasZeroObject (C i)] [∀ i, Preadditive (C i)]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive] [∀ i, Pretriangulated (C i)]
  [∀ i, CategoryTheory.Limits.HasZeroObject (D' i)] [∀ i, Preadditive (D' i)]
  [∀ i (n : ℤ), (shiftFunctor (D' i) n).Additive] [∀ i, Pretriangulated (D' i)]
  [CategoryTheory.Limits.HasZeroObject U.PairCategory] [Preadditive U.PairCategory]
  [∀ n : ℤ, (shiftFunctor U.PairCategory n).Additive] [Pretriangulated U.PairCategory]
  [CategoryTheory.Limits.HasZeroObject V.PairCategory] [Preadditive V.PairCategory]
  [∀ n : ℤ, (shiftFunctor V.PairCategory n).Additive] [Pretriangulated V.PairCategory]
  [∀ i, (V.ι i).IsTriangulated] [∀ i, (F.Φ i).IsTriangulated]
  [∀ i, (F.Φ i).IsEquivalence]

set_option linter.unusedVariables false in
private theorem reflection
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)
    (hsource : ∀ D : Triangle U.PairCategory, D ∈ distTriang U.PairCategory →
      ∃ (i : I) (A : Triangle (C i)), A ∈ distTriang (C i) ∧
        Nonempty (D ≅ (U.ι i).mapTriangle.obj A))
    (htarget : ∀ D : Triangle V.PairCategory, D ∈ distTriang V.PairCategory →
      ∃ (i : I) (A : Triangle (D' i)), A ∈ distTriang (D' i) ∧
        Nonempty (D ≅ (V.ι i).mapTriangle.obj A))
    (hhom : ∀ X Y, Function.Bijective (F.functor.map : (X ⟶ Y) → _)) :
    let := WeilConjectures.pairCommShift F hβ
    F.functor.IsTriangulated ∧
      (∀ D : Triangle U.PairCategory,
        F.functor.mapTriangle.obj D ∈ distTriang V.PairCategory ↔
          D ∈ distTriang U.PairCategory) ∧
      (∀ D : Triangle U.PairCategory,
        F.functor.mapTriangle.obj D ∈ distTriang V.PairCategory →
        ∃ (i : I) (A : Triangle (D' i)), A ∈ distTriang (D' i) ∧
        ∃ (R : D' i ⥤ C i) (adj : F.Φ i ⊣ R) (r : R.CommShift ℤ),
          (fun [inverseShift : R.CommShift ℤ] ↦
            adj.CommShift ℤ ∧ IsIso adj.unit ∧ IsIso adj.counit ∧ R.IsTriangulated ∧
            ∃ (α : F.functor.mapTriangle.obj D ≅ (V.ι i).mapTriangle.obj A)
              (β : D ≅ (U.ι i).mapTriangle.obj (R.mapTriangle.obj A))
              (e : F.functor.mapTriangle.obj
                ((U.ι i).mapTriangle.obj (R.mapTriangle.obj A)) ≅
                  (V.ι i).mapTriangle.obj A),
                HEq e.hom.hom₁ ((V.ι i).map (adj.counit.app A.obj₁)) ∧
                HEq e.hom.hom₂ ((V.ι i).map (adj.counit.app A.obj₂)) ∧
                HEq e.hom.hom₃ ((V.ι i).map (adj.counit.app A.obj₃)) ∧
                F.functor.mapTriangle.map β.hom ≫ e.hom = α.hom)
            (inverseShift := r)) ∧
      (∀ (R : V.PairCategory ⥤ U.PairCategory) (adj : F.functor ⊣ R)
        (r : R.CommShift ℤ),
        (fun [inverseShift : R.CommShift ℤ] ↦
          adj.CommShift ℤ → IsIso adj.unit → IsIso adj.counit → R.IsTriangulated)
          (inverseShift := r)) := by
  let := WeilConjectures.pairCommShift F hβ
  have : F.functor.Full := ⟨fun {X Y} ↦ (hhom X Y).2⟩
  have : F.functor.Faithful := ⟨fun {X Y} ↦ (hhom X Y).1⟩
  have hforward : F.functor.IsTriangulated := by
    constructor
    intro D hD
    obtain ⟨i, A, hA, ⟨e⟩⟩ := hsource D hD
    have := WeilConjectures.pairRestrictionShift F hβ i
    have : (U.ι i ⋙ F.functor).IsTriangulated :=
      Functor.isTriangulated_of_iso (F.ιCompFunctorIso i).symm
    exact mapTriangle_of_model F.functor (U.ι i) D A e
      ((U.ι i ⋙ F.functor).map_distinguished A hA)
  refine ⟨hforward, F.functor.map_distinguished_iff, ?_, ?_⟩
  · intro D hD
    obtain ⟨i, A, hA, ⟨α⟩⟩ := htarget _ hD
    obtain ⟨R, adj, r, hcomm, hunitR, hcounitR, hR, hc⟩ := finiteInverseTriangle (F.Φ i)
    let := r
    obtain ⟨c, hc₁, hc₂, hc₃⟩ := hc A
    obtain ⟨e, he₁, he₂, he₃⟩ :=
      finiteTriangleComparison F hβ i A R c adj.counit hc₁ hc₂ hc₃
    let β : D ≅ (U.ι i).mapTriangle.obj (R.mapTriangle.obj A) :=
      F.functor.mapTriangle.preimageIso (α ≪≫ e.symm)
    exact ⟨i, A, hA, R, adj, r, hcomm, hunitR, hcounitR, hR, α, β, e,
      he₁, he₂, he₃, preimageIso_comp F.functor.mapTriangle α e⟩
  · intro R adj r hcomm _ _
    let := r
    let := hcomm
    exact adj.isTriangulated_rightAdjoint

end Reflection

end ShiftTransport

private theorem coneIso (X Y : S.PairCategory) (M : I)
    (hX : X.stage ≤ M) (hY : Y.stage ≤ M) (Z : C M)
    (f : X.toStage hX ⟶ Y.toStage hY) (g : Y.toStage hY ⟶ Z)
    (h : Z ⟶ (X.toStage hX)⟦(1 : ℤ)⟧) :
    ∃ e : StageSystem.commonStageCone S X Y M hX hY Z f g h ≅
      (S.ι M).mapTriangle.obj (Triangle.mk f g h),
      e.hom.hom₁ = (S.isoToStage X hX).hom ∧
      e.hom.hom₂ = (S.isoToStage Y hY).hom ∧ e.hom.hom₃ = 𝟙 _ := by
  refine ⟨Triangle.isoMk _ _ (S.isoToStage X hX) (S.isoToStage Y hY)
    (Iso.refl _) ?_ ?_ ?_, rfl, rfl, rfl⟩
  · change StageSystem.PairCategory.mkHom M hX hY f ≫ (S.isoToStage Y hY).hom =
      (S.isoToStage X hX).hom ≫ (S.ι M).map f
    rw [StageSystem.mkHom_eq_isoToStage]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · change ((S.isoToStage Y hY).hom ≫ (S.ι M).map g) ≫ 𝟙 _ = _
    exact Category.comp_id _
  · change ((S.ι M).map h ≫ ((S.ι M).commShiftIso (1 : ℤ)).hom.app _ ≫
      (shiftFunctor S.PairCategory (1 : ℤ)).map (S.isoToStage X hX).inv) ≫
        (shiftFunctor S.PairCategory (1 : ℤ)).map (S.isoToStage X hX).hom =
      𝟙 _ ≫ ((S.ι M).map h ≫ ((S.ι M).commShiftIso (1 : ℤ)).hom.app _)
    erw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

set_option linter.unusedSectionVars false in
private theorem isoToStageHom (X : S.PairCategory) (M : I) (hX : X.stage ≤ M)
    (unit : S.T (le_refl M) ≅ 𝟭 (C M))
    (hunit : S.assoc hX (le_refl M) =
      Functor.isoWhiskerLeft (S.T hX) unit ≪≫ (S.T hX).rightUnitor) :
    (S.isoToStage X hX).hom =
      StageSystem.PairCategory.mkHom (X := X) (Y := ⟨M, X.toStage hX⟩)
        M hX le_rfl (unit.inv.app (X.toStage hX)) := by
  dsimp only [StageSystem.isoToStage]
  rw [hunit]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.id_comp]
  rfl

private theorem coneThird (X Y : S.PairCategory) (M : I)
    (hX : X.stage ≤ M) (hY : Y.stage ≤ M) (Z : C M)
    (f : X.toStage hX ⟶ Y.toStage hY) (g : Y.toStage hY ⟶ Z)
    (h : Z ⟶ (X.toStage hX)⟦(1 : ℤ)⟧)
    [NatTrans.CommShift (S.transIso hX).hom ℤ]
    (unit : S.T (le_refl M) ≅ 𝟭 (C M))
    (hunit : S.assoc hX (le_refl M) =
      Functor.isoWhiskerLeft (S.T hX) unit ≪≫ (S.T hX).rightUnitor) :
    (StageSystem.commonStageCone S X Y M hX hY Z f g h).mor₃ =
      StageSystem.PairCategory.mkHom
        (X := ⟨M, Z⟩) (Y := ⟨X.stage, X.obj⟦(1 : ℤ)⟧⟩) M le_rfl hX
        (unit.hom.app Z ≫ h ≫ ((S.T hX).commShiftIso (1 : ℤ)).inv.app X.obj) := by
  have hshift := NatTrans.shift_app_comm (S.transIso hX).hom (1 : ℤ) X.obj
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj] at hshift
  change ((S.ι M).map (((S.T hX).commShiftIso (1 : ℤ)).hom.app X.obj) ≫
    𝟙 _) ≫ (shiftFunctor S.PairCategory (1 : ℤ)).map (S.isoToStage X hX).inv =
    (S.isoToStage (X⟦(1 : ℤ)⟧) hX).inv ≫ 𝟙 _ at hshift
  simp only [Category.comp_id] at hshift
  have hs : (shiftFunctor S.PairCategory (1 : ℤ)).map (S.isoToStage X hX).inv =
      (S.ι M).map (((S.T hX).commShiftIso (1 : ℤ)).inv.app X.obj) ≫
        (S.isoToStage (X⟦(1 : ℤ)⟧) hX).inv := by
    rw [← hshift]
    erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  change (S.ι M).map h ≫ 𝟙 _ ≫
    (shiftFunctor S.PairCategory (1 : ℤ)).map (S.isoToStage X hX).inv = _
  erw [Category.id_comp]
  rw [hs]
  erw [← Functor.map_comp_assoc]
  rw [StageSystem.ι_map_eq (le_refl M)]
  dsimp only [StageSystem.isoToStage]
  erw [StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  erw [hunit]
  change (S.T (le_refl M)).map
      (h ≫ ((S.T hX).commShiftIso (1 : ℤ)).inv.app X.obj) ≫
        (unit.hom.app _ ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact unit.hom.naturality _

private theorem eqToIso_whiskerLeft
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (F : A ⥤ B) {G H : B ⥤ D} (h : G = H) :
    eqToIso (congrArg (fun K ↦ F ⋙ K) h) = Functor.isoWhiskerLeft F (eqToIso h) := by
  subst H
  rfl

private theorem identification (X Y : S.PairCategory) (M : I)
    (hX : X.stage ≤ M) (hY : Y.stage ≤ M) (Z : C M)
    (f : X.toStage hX ⟶ Y.toStage hY) (g : Y.toStage hY ⟶ Z)
    (h : Z ⟶ (X.toStage hX)⟦(1 : ℤ)⟧)
    [NatTrans.CommShift (S.transIso hX).hom ℤ]
    (unit : S.T (le_refl M) ≅ 𝟭 (C M))
    (hunitX : S.assoc hX (le_refl M) =
      Functor.isoWhiskerLeft (S.T hX) unit ≪≫ (S.T hX).rightUnitor)
    (hunitY : S.assoc hY (le_refl M) =
      Functor.isoWhiskerLeft (S.T hY) unit ≪≫ (S.T hY).rightUnitor) :
    ∃ e : StageSystem.commonStageCone S
        X Y M hX hY Z f g h ≅
      (S.ι M).mapTriangle.obj
        (Triangle.mk f g h),
      e.hom.hom₁ = (S.isoToStage X hX).hom ∧
      e.hom.hom₂ = (S.isoToStage Y hY).hom ∧
      e.hom.hom₃ = 𝟙 _ ∧
      HEq e.hom.hom₁
        (StageSystem.PairCategory.mkHom
          (X := X) (Y := ⟨M, X.toStage hX⟩) M hX le_rfl
          (unit.inv.app (X.toStage hX))) ∧
      HEq e.hom.hom₂
        (StageSystem.PairCategory.mkHom
          (X := Y) (Y := ⟨M, Y.toStage hY⟩) M hY le_rfl
          (unit.inv.app (Y.toStage hY))) ∧
      HEq (StageSystem.commonStageCone S
        X Y M hX hY Z f g h).mor₃
        (StageSystem.PairCategory.mkHom
          (X := ⟨M, Z⟩) (Y := ⟨X.stage, X.obj⟦(1 : ℤ)⟧⟩) M le_rfl hX
          (unit.hom.app Z ≫ h ≫
            ((S.T hX).commShiftIso (1 : ℤ)).inv.app X.obj)) := by
  obtain ⟨e, he₁, he₂, he₃⟩ := coneIso S X Y M hX hY Z f g h
  refine ⟨e, he₁, he₂, he₃, ?_, ?_, ?_⟩
  · apply heq_of_eq
    rw [he₁]
    exact isoToStageHom S X M hX unit hunitX
  · apply heq_of_eq
    rw [he₂]
    exact isoToStageHom S Y M hY unit hunitY
  · exact heq_of_eq (coneThird S X Y M hX hY Z f g h unit hunitX)

end FdConeProof

universe d u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] pbcScalarExtension pbcScalarAssociator
  pbcScalarCommShift pbcRationalHasShift pbcIntegralDatum HasDerivedCategory.standard
  ScalarLocalization.composition ScalarLocalization.category
  SheafOfModules.instAbelian SheafOfModules.instCategory
  instCategoryDerivedCategory DerivedCategory.instPreadditive

namespace WeilConjectures

attribute [local irreducible] pairShiftIso pairStageShiftIso

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (W : Scheme.{u}) [IsNoetherian W]
  [dW : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
  [iW : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

/-- The framework identity transition with its prescribed tensor unit.
Source: trace-definition final sentence, identity normalization
(blueprint: lem-fd-shift-triangle-reflection). -/
@[irreducible] def fdFrameworkStageUnit (E : Padic.FiniteCoefficientFields l Ω) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W).T (le_refl E) ≅
      𝟭 (GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E) :=
  eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l Ω W).exists.choose_spec.1 E E (le_refl E)) ≪≫
    GeneralAlgebraicallyClosedCoefficients.unitor l Ω W E

/-- The literal PBC identity transition's canonical equality isomorphism.
Source: trace-definition final sentence, identity normalization
(blueprint: lem-fd-shift-triangle-reflection). -/
@[irreducible] def fdPbcStageUnit (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcScalarSystem l Ω W dW.out iW.out).T (le_refl E) ≅
      𝟭 (pbcStageCategory l Ω W E) :=
  eqToIso (pbcScalarSystem_units l Ω W dW.out iW.out (le_refl E)).1

/-- The actual finite scalar shift at an explicitly named coefficient stage.
Source: trace-definition final sentence, common-stage connecting-arrow formula
(blueprint: lem-fd-shift-triangle-reflection). -/
@[irreducible] def fdPbcScalarShift
    (E M : Padic.FiniteCoefficientFields l Ω) (h : E ≤ M)
    (K : pbcStageCategory l Ω W E) :
    (pbcScalarExtension l Ω W dW.out iW.out h).obj (K⟦(1 : ℤ)⟧) ≅
      ((pbcScalarExtension l Ω W dW.out iW.out h).obj K)⟦(1 : ℤ)⟧ :=
  ((pbcScalarExtension l Ω W dW.out iW.out h).commShiftIso (1 : ℤ)).app K

section DescentProof
attribute [local irreducible] StageSystem.Morphism.functor StageSystem.ι

section Descent
variable (J : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W)
    (pbcScalarSystem l Ω W dW.out iW.out))
  [∀ E, (J.Φ E).CommShift ℤ]
  (hshift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (J.β h).hom ℤ)

private theorem fdRestriction (E : Padic.FiniteCoefficientFields l Ω) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W).ι E ⋙ J.functor =
      J.Φ E ⋙ (pbcScalarSystem l Ω W dW.out iW.out).ι E := by
  exact FdConeProof.restriction_eq J E

set_option backward.defeqAttrib.useBackward true in
private theorem fdDescendedShiftSpec :
    let := pairCommShift J hshift
    ∀ (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E),
      HEq ((J.functor.commShiftIso n).hom.app ⟨E, K⟩)
        (((pbcScalarSystem l Ω W dW.out iW.out).ι E).map
          (((J.Φ E).commShiftIso n).hom.app K)) ∧
      HEq ((J.functor.commShiftIso n).inv.app ⟨E, K⟩)
        (((pbcScalarSystem l Ω W dW.out iW.out).ι E).map
          (((J.Φ E).commShiftIso n).inv.app K)) := by
  dsimp only [GeneralAlgebraicallyClosedCoefficients.pairCategory,
    GeneralAlgebraicallyClosedCoefficients.inclusion]
  intro E n K
  change HEq ((pairShiftIso J hshift n).hom.app ⟨E, K⟩) _ ∧
    HEq ((pairShiftIso J hshift n).inv.app ⟨E, K⟩) _
  obtain ⟨q, hq⟩ := FdConeProof.inclusionShift_normalized
    (pbcScalarSystem l Ω W dW.out iW.out) E n ((J.Φ E).obj K)
  exact FdConeProof.pairShift_normalized J hshift n E K
    (framework_shift_obj n E K) q (framework_inclusion_shift_inv n E K) hq

end Descent

set_option linter.unusedVariables false in
/-- The finite shift comparisons descend, and the resulting functor preserves and
reflects distinguished triangles with a compatible finite inverse model.
Source: trace-definition final sentence, common-stage comparison steps 6--8
(blueprint: lem-fd-shift-triangle-reflection).

Proof: (1) At a representative [M,u], expand the shifted representative and the
conjugation by j. Scalar-shift compatibility at the target, naturality of the
finite delta at u, and compatibility at the source give naturality of [E,delta].
(2) Include the finite inverse components to obtain the inverse; repeat for every
integer shift. Zero and addition coherence hold at the object's own finite stage.
(3) The endpoint stage isomorphisms identify each target common-stage cone with
the inclusion of its finite cone, including the inverse scalar-shift in its last
arrow (fdCommonStageConeIdentification below). (4) A source distinguished triangle
has a finite distinguished model. Finite exactness and (3) show its image is
distinguished. (5) Given a distinguished image, choose its finite model A and an
exact inverse R to the finite equivalence, with the adjunction-induced shift.
The counit gives e from J of the included R A to the inclusion of A.
(6) Lift e inverse composed with alpha using the assumed Hom bijections.
Faithfulness gives the inverse equations and the first two triangle squares.
For the last square use descended shift naturality and cancel its isomorphism.
This produces beta and the equation J(beta) followed by e equals alpha.
(7) Every target pair is in the essential image by its finite counit. For any
quasi-inverse with adjunction-compatible shifts apply the exact-equivalence-inverse
lemma (Mathlib Equivalence.IsTriangulated.mk'). All objects remain literal pairs. -/
theorem fdShiftTriangleReflection
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p)
    (J : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W)
      (pbcScalarSystem l Ω W dW.out iW.out))
    [∀ E, (J.Φ E).CommShift ℤ]
    [∀ E, (J.Φ E).Additive]
    [∀ E, (J.Φ E).IsEquivalence]
    [∀ E, (J.Φ E).Linear E.val]
    [∀ E, (J.Φ E).IsTriangulated]
    (hunit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E),
      (J.β (le_refl E)).hom.app K ≫ (J.Φ E).map
        ((fdFrameworkStageUnit l Ω W E).hom.app K) =
        (fdPbcStageUnit l Ω W E).hom.app ((J.Φ E).obj K))
    (hshift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (J.β h).hom ℤ)
    [J.functor.Additive]
    (hhom : ∀ X Y, Function.Bijective (J.functor.map : (X ⟶ Y) → _)) :
    ∃ s : J.functor.CommShift ℤ,
      (fun [shiftInst : J.functor.CommShift ℤ] ↦
        (∀ (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ)
          (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E),
          HEq ((J.functor.commShiftIso n).hom.app ⟨E, K⟩)
            (((pbcScalarSystem l Ω W dW.out iW.out).ι E).map
              (((J.Φ E).commShiftIso n).hom.app K)) ∧
          HEq ((J.functor.commShiftIso n).inv.app ⟨E, K⟩)
            (((pbcScalarSystem l Ω W dW.out iW.out).ι E).map
              (((J.Φ E).commShiftIso n).inv.app K))) ∧
        (∀ E, (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W).ι E ⋙
          J.functor = J.Φ E ⋙ (pbcScalarSystem l Ω W dW.out iW.out).ι E) ∧
        J.functor.IsTriangulated ∧
        (∀ D : Triangle (generalAlgebraicallyClosedConstructibleCategory l Ω W),
          J.functor.mapTriangle.obj D ∈ distTriang (pbcQbarCategory l Ω W) ↔
            D ∈ distTriang (generalAlgebraicallyClosedConstructibleCategory l Ω W)) ∧
        (∀ D : Triangle (generalAlgebraicallyClosedConstructibleCategory l Ω W),
          J.functor.mapTriangle.obj D ∈ distTriang (pbcQbarCategory l Ω W) →
          ∃ (M : Padic.FiniteCoefficientFields l Ω)
            (A : Triangle (pbcStageCategory l Ω W M)),
            A ∈ distTriang (pbcStageCategory l Ω W M) ∧
            ∃ (R : pbcStageCategory l Ω W M ⥤
                GeneralAlgebraicallyClosedCoefficients.Stage l Ω W M)
              (adj : J.Φ M ⊣ R) (r : R.CommShift ℤ),
              (fun [inverseShift : R.CommShift ℤ] ↦
                adj.CommShift ℤ ∧ IsIso adj.unit ∧ IsIso adj.counit ∧
                R.IsTriangulated ∧
                ∃ (α : J.functor.mapTriangle.obj D ≅
                    ((pbcScalarSystem l Ω W dW.out iW.out).ι M).mapTriangle.obj A)
                  (β : D ≅
                    ((GeneralAlgebraicallyClosedCoefficients.inclusion
                      (l := l) (Ω := Ω) (Y := W) M)).mapTriangle.obj
                      (R.mapTriangle.obj A))
                  (e : J.functor.mapTriangle.obj
                      (((GeneralAlgebraicallyClosedCoefficients.inclusion
                      (l := l) (Ω := Ω) (Y := W) M)).mapTriangle.obj
                        (R.mapTriangle.obj A)) ≅
                    ((pbcScalarSystem l Ω W dW.out iW.out).ι M).mapTriangle.obj A),
                  HEq e.hom.hom₁
                    (((pbcScalarSystem l Ω W dW.out iW.out).ι M).map
                      (adj.counit.app A.obj₁)) ∧
                  HEq e.hom.hom₂
                    (((pbcScalarSystem l Ω W dW.out iW.out).ι M).map
                      (adj.counit.app A.obj₂)) ∧
                  HEq e.hom.hom₃
                    (((pbcScalarSystem l Ω W dW.out iW.out).ι M).map
                      (adj.counit.app A.obj₃)) ∧
                  J.functor.mapTriangle.map β.hom ≫ e.hom = α.hom)
                (inverseShift := r)) ∧
        (∀ (R : pbcQbarCategory l Ω W ⥤
            generalAlgebraicallyClosedConstructibleCategory l Ω W)
          (adj : J.functor ⊣ R) (r : R.CommShift ℤ),
          (fun [inverseShift : R.CommShift ℤ] ↦
            adj.CommShift ℤ → IsIso adj.unit → IsIso adj.counit → R.IsTriangulated)
            (inverseShift := r))) (shiftInst := s) := by
  dsimp only [GeneralAlgebraicallyClosedCoefficients.pairCategory,
    GeneralAlgebraicallyClosedCoefficients.inclusion]
  have _ := hunit
  let := pairCommShift J hshift
  let : ∀ E, ((pbcScalarSystem l Ω W dW.out iW.out).ι E).IsTriangulated :=
    fun E ↦ (pbcVerdierAxioms l Ω W).2.1 E
  have hm := (StageSystem.commonStage_verdier_existsUnique
    (pbcScalarSystem l Ω W dW.out iW.out)).exists.choose_spec.1
  obtain ⟨hf, hr, hm, hi⟩ := FdConeProof.reflection J hshift
    (fun D hD ↦ (GeneralAlgebraicallyClosedCoefficients.distinguished_iff D).mp hD)
    (fun D hD ↦ (hm D).mp hD) hhom
  exact ⟨inferInstance, fdDescendedShiftSpec l Ω W J hshift,
    fdRestriction l Ω W J, hf, hr, hm, hi⟩

end DescentProof

private theorem fdPbcRightUnit
    {E M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ M) :
    (pbcScalarSystem l Ω W dW.out iW.out).assoc h (le_refl M) =
      Functor.isoWhiskerLeft (pbcScalarExtension l Ω W dW.out iW.out h)
        (fdPbcStageUnit l Ω W M) ≪≫
          (pbcScalarExtension l Ω W dW.out iW.out h).rightUnitor := by
  change pbcScalarAssociator l Ω W dW.out iW.out h (le_refl M) = _
  rw [pbcScalarAssociator_rightUnit l Ω W dW.out iW.out h
    (pbcScalarSystem_units l Ω W dW.out iW.out (le_refl M)).1]
  unfold fdPbcStageUnit
  congr 1
  exact FdConeProof.eqToIso_whiskerLeft _ _

attribute [local instance] StageSystem.pbcPairHasShift
  StageSystem.pbcStageInclusionCommShift

set_option linter.unusedVariables false in
/-- Every common-stage cone is the included finite cone, with the endpoint classes
and the inverse scalar-shift in its third arrow.
Source: trace-definition final sentence, common-stage comparison step 3
(blueprint: lem-fd-shift-triangle-reflection).

Proof: take isoToStage at the two endpoints and the identity at the cone object.
The first square is the representative formula for the first arrow, and the
second is the definition of commonStageCone. For the last square, shifting the
first endpoint identity class inserts sigma; it cancels the inverse sigma in the
third arrow. The endpoint maps are represented by identities since the repeated
stage transitions and their unit associators are normalized. Thus all three
squares hold, giving the specified triangle isomorphism, including zero arrows. -/
theorem fdCommonStageConeIdentification
    (X Y : pbcQbarCategory l Ω W) (M : Padic.FiniteCoefficientFields l Ω)
    (hX : X.stage ≤ M) (hY : Y.stage ≤ M)
    (Z : pbcStageCategory l Ω W M)
    (f : X.toStage hX ⟶ Y.toStage hY) (g : Y.toStage hY ⟶ Z)
    (h : Z ⟶ (X.toStage hX)⟦(1 : ℤ)⟧)
    (hdist : Triangle.mk f g h ∈ distTriang (pbcStageCategory l Ω W M)) :
    ∃ e : StageSystem.commonStageCone (pbcScalarSystem l Ω W dW.out iW.out)
        X Y M hX hY Z f g h ≅
      ((pbcScalarSystem l Ω W dW.out iW.out).ι M).mapTriangle.obj
        (Triangle.mk f g h),
      e.hom.hom₁ = ((pbcScalarSystem l Ω W dW.out iW.out).isoToStage X hX).hom ∧
      e.hom.hom₂ = ((pbcScalarSystem l Ω W dW.out iW.out).isoToStage Y hY).hom ∧
      e.hom.hom₃ = 𝟙 _ ∧
      HEq e.hom.hom₁
        (StageSystem.PairCategory.mkHom
          (X := X) (Y := ⟨M, X.toStage hX⟩) M hX le_rfl
          ((fdPbcStageUnit l Ω W M).inv.app (X.toStage hX))) ∧
      HEq e.hom.hom₂
        (StageSystem.PairCategory.mkHom
          (X := Y) (Y := ⟨M, Y.toStage hY⟩) M hY le_rfl
          ((fdPbcStageUnit l Ω W M).inv.app (Y.toStage hY))) ∧
      HEq (StageSystem.commonStageCone (pbcScalarSystem l Ω W dW.out iW.out)
        X Y M hX hY Z f g h).mor₃
        (StageSystem.PairCategory.mkHom
          (X := ⟨M, Z⟩) (Y := ⟨X.stage, X.obj⟦(1 : ℤ)⟧⟩) M le_rfl hX
          ((fdPbcStageUnit l Ω W M).hom.app Z ≫ h ≫
            (fdPbcScalarShift l Ω W X.stage M hX X.obj).inv)) := by
  unfold fdPbcScalarShift
  exact FdConeProof.identification
    (C := fun E : Padic.FiniteCoefficientFields l Ω ↦ pbcStageCategory l Ω W E)
    (pbcScalarSystem l Ω W dW.out iW.out) X Y M hX hY Z f g h
    (fdPbcStageUnit l Ω W M) (fdPbcRightUnit l Ω W hX) (fdPbcRightUnit l Ω W hY)

end WeilConjectures
