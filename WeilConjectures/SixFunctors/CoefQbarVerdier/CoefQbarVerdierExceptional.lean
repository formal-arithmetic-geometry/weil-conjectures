/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.CategoryTheory.StageSystem.Morphism.StageSystemAdjunction
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarFiniteScalarCocycles
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarFiniteExceptionalFormula

/-! # Descent of the finite exceptional adjunction

Source: blueprint thm-coef-qbar-verdier, proof steps 6--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  WeilConjectures.CoefQbarPullback
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory
  WeilConjectures.sfRationalScalarExtension WeilConjectures.sfRationalScalarComp
  WeilConjectures.sfRationalScalarUnit WeilConjectures.sfRationalConstructibleLocalization
  CategoryTheory.ScalarLocalization.category CategoryTheory.ScalarLocalization.composition

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

private def adjustBeta
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁)
    {U U' : C₀ ⥤ C₁} {V V' : D₀ ⥤ D₁} (eU : U = U') (eV : V = V')
    (b : F₀ ⋙ V' ≅ U' ⋙ F₁) : F₀ ⋙ V ≅ U ⋙ F₁ :=
  Functor.isoWhiskerLeft F₀ (eqToIso eV) ≪≫ b ≪≫
    Functor.isoWhiskerRight (eqToIso eU.symm) F₁

private theorem adjustBeta_coherent
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    {U₀ U₀' : C₀ ⥤ C₁} {U₁ U₁' : C₁ ⥤ C₂} {U₂ U₂' : C₀ ⥤ C₂}
    {V₀ V₀' : D₀ ⥤ D₁} {V₁ V₁' : D₁ ⥤ D₂} {V₂ V₂' : D₀ ⥤ D₂}
    (eU₀ : U₀ = U₀') (eU₁ : U₁ = U₁') (eU₂ : U₂ = U₂')
    (eV₀ : V₀ = V₀') (eV₁ : V₁ = V₁') (eV₂ : V₂ = V₂')
    (aU : U₀ ⋙ U₁ ≅ U₂) (aU' : U₀' ⋙ U₁' ≅ U₂')
    (aV : V₀ ⋙ V₁ ≅ V₂) (aV' : V₀' ⋙ V₁' ≅ V₂')
    (haU : HEq aU aU') (haV : HEq aV aV')
    (b₀ : F₀ ⋙ V₀' ≅ U₀' ⋙ F₁) (b₁ : F₁ ⋙ V₁' ≅ U₁' ⋙ F₂)
    (b₂ : F₀ ⋙ V₂' ≅ U₂' ⋙ F₂)
    (h : ∀ x, V₁'.map (b₀.hom.app x) ≫ b₁.hom.app (U₀'.obj x) ≫
      F₂.map (aU'.hom.app x) = aV'.hom.app (F₀.obj x) ≫ b₂.hom.app x)
    (x : C₀) :
    V₁.map ((adjustBeta F₀ F₁ eU₀ eV₀ b₀).hom.app x) ≫
      (adjustBeta F₁ F₂ eU₁ eV₁ b₁).hom.app (U₀.obj x) ≫ F₂.map (aU.hom.app x) =
    aV.hom.app (F₀.obj x) ≫ (adjustBeta F₀ F₂ eU₂ eV₂ b₂).hom.app x := by
  subst U₀' U₁' U₂' V₀' V₁' V₂'
  cases eq_of_heq haU
  cases eq_of_heq haV
  simpa [adjustBeta] using h x

private theorem adjustBeta_unit
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁]
    {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁} {G₀ : D₀ ⥤ C₀} {G₁ : D₁ ⥤ C₁}
    (a₀ : F₀ ⊣ G₀) (a₁ : F₁ ⊣ G₁)
    {U U' : C₀ ⥤ C₁} {V V' : D₀ ⥤ D₁} (eU : U = U') (eV : V = V')
    (q : F₀ ⋙ V' ≅ U' ⋙ F₁) (b : G₀ ⋙ U' ≅ V' ⋙ G₁)
    (h : ∀ x, U'.map (a₀.unit.app x) ≫ b.hom.app (F₀.obj x) ≫
      G₁.map (q.hom.app x) = a₁.unit.app (U'.obj x)) (x : C₀) :
    U.map (a₀.unit.app x) ≫ (adjustBeta G₀ G₁ eV eU b).hom.app (F₀.obj x) ≫
      G₁.map ((adjustBeta F₀ F₁ eU eV q).hom.app x) = a₁.unit.app (U.obj x) := by
  subst U' V'
  simpa [adjustBeta] using h x

private theorem adjustBeta_counit
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁]
    {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁} {G₀ : D₀ ⥤ C₀} {G₁ : D₁ ⥤ C₁}
    (a₀ : F₀ ⊣ G₀) (a₁ : F₁ ⊣ G₁)
    {U U' : C₀ ⥤ C₁} {V V' : D₀ ⥤ D₁} (eU : U = U') (eV : V = V')
    (q : F₀ ⋙ V' ≅ U' ⋙ F₁) (b : G₀ ⋙ U' ≅ V' ⋙ G₁)
    (h : ∀ y, q.hom.app (G₀.obj y) ≫ F₁.map (b.hom.app y) ≫
      a₁.counit.app (V'.obj y) = V'.map (a₀.counit.app y)) (y : D₀) :
    (adjustBeta F₀ F₁ eU eV q).hom.app (G₀.obj y) ≫
      F₁.map ((adjustBeta G₀ G₁ eV eU b).hom.app y) ≫
      a₁.counit.app (V.obj y) = V.map (a₀.counit.app y) := by
  subst U' V'
  simpa [adjustBeta] using h y

private theorem scalar_square
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category* (C i)] [∀ i, Category* (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    {i j : I} (h : i ≤ j) (x : C i) :
    (T.ι j).map ((F.β h).hom.app x) =
      (T.transIso h).hom.app ((F.Φ i).obj x) ≫
        F.functor.map ((S.transIso h).inv.app x) := by
  apply (cancel_mono (F.functor.map ((S.transIso h).hom.app x))).mp
  erw [Category.assoc, ← F.functor.map_comp, Iso.inv_hom_id_app, F.functor.map_id,
    Category.comp_id]
  erw [StageSystem.transIso_hom_app_eq, F.functor_map_mkHom,
    StageSystem.transIso_hom_app_eq, StageSystem.ι_map_eq le_rfl,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom j le_rfl h)
  dsimp only [StageSystem.Morphism.mapAt, StageSystem.PairCategory.toStage,
    StageSystem.Morphism.functor]
  have H := congrArg (fun t ↦ t ≫ (F.β h).inv.app x) (F.coh h le_rfl x)
  simpa only [Functor.comp_obj, StageSystem.ι, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id] using H

private theorem adjusted_scalar_square
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category* (C i)] [∀ i, Category* (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    {i j : I} (h : i ≤ j) {U : C i ⥤ C j} {V : D i ⥤ D j}
    (eU : S.T h = U) (eV : T.T h = V)
    (b : F.Φ i ⋙ V ≅ U ⋙ F.Φ j)
    (hb : F.β h = adjustBeta _ _ eU eV b) (x : C i) :
    (T.ι j).map (b.hom.app x) =
      ((eqToIso (congrArg (fun W ↦ W ⋙ T.ι j) eV.symm) ≪≫ T.transIso h).hom.app
        ((F.Φ i).obj x)) ≫
      F.functor.map
        ((eqToIso (congrArg (fun W ↦ W ⋙ S.ι j) eU.symm) ≪≫ S.transIso h).inv.app x) := by
  subst U V
  have hb' : F.β h = b := by
    ext z
    simpa [adjustBeta] using congrArg (fun e ↦ e.hom.app z) hb
  simpa only [hb', eqToIso_refl, Iso.refl_trans] using scalar_square F h x

private theorem comparison_cube {C : Type*} [Category* C]
    {P₀ P₁ P₂ Q₀ Q₁ R₀ R₁ : C}
    (b : P₀ ≅ P₁) (a₀ : P₂ ≅ Q₀) (a₁ : P₁ ≅ Q₁) (t : P₀ ≅ P₂)
    (u : Q₁ ≅ Q₀) (v : R₁ ≅ R₀) (e₀ : P₂ ≅ R₀) (e₁ : P₁ ≅ R₁)
    (ha : b.hom ≫ a₁.hom = t.hom ≫ a₀.hom ≫ u.inv)
    (he : b.hom ≫ e₁.hom = t.hom ≫ e₀.hom ≫ v.inv) :
    u.hom ≫ (a₀.symm ≪≫ e₀).hom = (a₁.symm ≪≫ e₁).hom ≫ v.hom := by
  apply (cancel_epi (b.hom ≫ a₁.hom)).mp
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    _ = t.hom ≫ e₀.hom := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] using
        congrArg (fun r ↦ r ≫ u.hom ≫ a₀.inv ≫ e₀.hom) ha
    _ = b.hom ≫ e₁.hom ≫ v.hom := by
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        (congrArg (fun r ↦ r ≫ v.hom) he).symm
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem adjust_nat_square
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category* (C i)] {D : Type*} [Category* D]
    (S : StageSystem C) (F G : S.PairCategory ⥤ D)
    (e : ∀ i, S.ι i ⋙ F ≅ S.ι i ⋙ G)
    {i j : I} (h : i ≤ j) {U : C i ⥤ C j} (hU : S.T h = U) (x : C i)
    (he : F.map
        ((eqToIso (congrArg (fun W ↦ W ⋙ S.ι j) hU.symm) ≪≫ S.transIso h).hom.app x) ≫
        (e i).hom.app x = (e j).hom.app (U.obj x) ≫
      G.map
        ((eqToIso (congrArg (fun W ↦ W ⋙ S.ι j) hU.symm) ≪≫ S.transIso h).hom.app x)) :
    F.map ((S.transIso h).hom.app x) ≫ (e i).hom.app x =
      (e j).hom.app ((S.T h).obj x) ≫ G.map ((S.transIso h).hom.app x) := by
  subst U
  simpa using he

private theorem inverse_square {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) {X Y : C} (t : X ≅ Y)
    (eX : F.obj X ≅ G.obj X) (eY : F.obj Y ≅ G.obj Y)
    (h : F.map t.hom ≫ eY.hom = eX.hom ≫ G.map t.hom) :
    F.map t.inv ≫ eX.hom = eY.hom ≫ G.map t.inv := by
  apply (cancel_mono (G.map t.hom)).mp
  simp only [Category.assoc]
  rw [← G.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id, ← h, ← Category.assoc, ← F.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem three_squares {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) {W X Y Z : C} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (eW : F.obj W ⟶ G.obj W) (eX : F.obj X ⟶ G.obj X)
    (eY : F.obj Y ⟶ G.obj Y) (eZ : F.obj Z ⟶ G.obj Z)
    (ha : F.map a ≫ eX = eW ≫ G.map a)
    (hb : F.map b ≫ eY = eX ≫ G.map b)
    (hc : F.map c ≫ eZ = eY ≫ G.map c) :
    F.map (a ≫ b ≫ c) ≫ eZ = eW ≫ G.map (a ≫ b ≫ c) := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hc, ← Category.assoc (F.map b), hb]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map a), ha]
  simp only [Category.assoc]

private def glueStageIso
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category* (C i)] {D : Type*} [Category* D]
    (S : StageSystem C) (F G : S.PairCategory ⥤ D)
    (e : ∀ i, S.ι i ⋙ F ≅ S.ι i ⋙ G)
    (he : ∀ {i j} (h : i ≤ j) (x : C i),
      F.map ((S.transIso h).hom.app x) ≫ (e i).hom.app x =
        (e j).hom.app ((S.T h).obj x) ≫ G.map ((S.transIso h).hom.app x)) : F ≅ G :=
  NatIso.ofComponents (fun P ↦ (e P.stage).app P.obj) (fun {P Q} f ↦ by
    rcases P with ⟨i, x⟩
    rcases Q with ⟨j, y⟩
    change F.map f ≫ (e j).hom.app y = (e i).hom.app x ≫ G.map f
    obtain ⟨n, hP, hQ, u, hf⟩ := S.exists_stage_representation.2.1 x y f
    have hi : F.map ((S.transIso hP).inv.app x) ≫
        (e n).hom.app ((S.T hP).obj x) =
        (e i).hom.app x ≫ G.map ((S.transIso hP).inv.app x) := by
      exact inverse_square F G ((S.transIso hP).app x)
        ((e n).app ((S.T hP).obj x)) ((e i).app x) (he hP x)
    have hall := three_squares F G
      ((S.transIso hP).inv.app x) ((S.ι n).map u) ((S.transIso hQ).hom.app y)
      ((e i).hom.app x) ((e n).hom.app ((S.T hP).obj x))
      ((e n).hom.app ((S.T hQ).obj y)) ((e j).hom.app y)
      hi ((e n).hom.naturality u) (he hQ y)
    subst f
    exact hall)

namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition associator unitor)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

private abbrev stages (Z : Scheme.{u}) :=
  GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z

private theorem transition_eq (Z : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L) :
    (stages l Ω Z).T h = transition l Ω Z E L h :=
  (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Z).exists.choose_spec.1
    E L h

private def leftBeta (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    {E L : Index l Ω} (h : E ≤ L) :
    finiteLeft D l hl Ω X f c S E ⋙ (stages l Ω Y).T h ≅
      (stages l Ω X).T h ⋙ finiteLeft D l hl Ω X f c S L :=
  adjustBeta _ _ (transition_eq l Ω X E L h) (transition_eq l Ω Y E L h)
    (finiteLeftScalar D l hl Ω X f c S E L h)

private def rightBeta (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    {E L : Index l Ω} (h : E ≤ L) :
    finiteRight D l hl Ω X f c S E ⋙ (stages l Ω X).T h ≅
      (stages l Ω Y).T h ⋙ finiteRight D l hl Ω X f c S L :=
  adjustBeta _ _ (transition_eq l Ω Y E L h) (transition_eq l Ω X E L h)
    (finiteRightScalar D l hl Ω X f c S E L h)

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
private theorem left_coherent (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) (K : Stage l Ω X E) :
    ((stages l Ω Y).T k).map ((leftBeta D l hl Ω X f c S h).hom.app K) ≫
      (leftBeta D l hl Ω X f c S k).hom.app (((stages l Ω X).T h).obj K) ≫
      (finiteLeft D l hl Ω X f c S M).map
        (((stages l Ω X).assoc h k).hom.app K) =
    ((stages l Ω Y).assoc h k).hom.app ((finiteLeft D l hl Ω X f c S E).obj K) ≫
      (leftBeta D l hl Ω X f c S (h.trans k)).hom.app K := by
  refine adjustBeta_coherent (finiteLeft D l hl Ω X f c S E)
    (finiteLeft D l hl Ω X f c S L) (finiteLeft D l hl Ω X f c S M)
    (transition_eq l Ω X E L h) (transition_eq l Ω X L M k)
    (transition_eq l Ω X E M (h.trans k))
    (transition_eq l Ω Y E L h) (transition_eq l Ω Y L M k)
    (transition_eq l Ω Y E M (h.trans k))
    _ (associator l Ω X E L M h k) _ (associator l Ω Y E L M h k)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω X).exists.choose_spec.2 E L M h k)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω Y).exists.choose_spec.2 E L M h k)
    (finiteLeftScalar D l hl Ω X f c S E L h)
    (finiteLeftScalar D l hl Ω X f c S L M k)
    (finiteLeftScalar D l hl Ω X f c S E M (h.trans k)) ?_ K
  exact (finite_scalar_cocycles D l hl Ω X f c S h k).1.equation

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
private theorem right_coherent (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) (K : Stage l Ω Y E) :
    ((stages l Ω X).T k).map ((rightBeta D l hl Ω X f c S h).hom.app K) ≫
      (rightBeta D l hl Ω X f c S k).hom.app (((stages l Ω Y).T h).obj K) ≫
      (finiteRight D l hl Ω X f c S M).map
        (((stages l Ω Y).assoc h k).hom.app K) =
    ((stages l Ω X).assoc h k).hom.app ((finiteRight D l hl Ω X f c S E).obj K) ≫
      (rightBeta D l hl Ω X f c S (h.trans k)).hom.app K := by
  refine adjustBeta_coherent (finiteRight D l hl Ω X f c S E)
    (finiteRight D l hl Ω X f c S L) (finiteRight D l hl Ω X f c S M)
    (transition_eq l Ω Y E L h) (transition_eq l Ω Y L M k)
    (transition_eq l Ω Y E M (h.trans k))
    (transition_eq l Ω X E L h) (transition_eq l Ω X L M k)
    (transition_eq l Ω X E M (h.trans k))
    _ (associator l Ω Y E L M h k) _ (associator l Ω X E L M h k)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω Y).exists.choose_spec.2 E L M h k)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω X).exists.choose_spec.2 E L M h k)
    (finiteRightScalar D l hl Ω X f c S E L h)
    (finiteRightScalar D l hl Ω X f c S L M k)
    (finiteRightScalar D l hl Ω X f c S E M (h.trans k)) ?_ K
  exact (finite_scalar_cocycles D l hl Ω X f c S h k).2.equation

private def leftMorphism (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)) :
    (stages l Ω X).Morphism (stages l Ω Y) where
  Φ := finiteLeft D l hl Ω X f c S
  β := leftBeta D l hl Ω X f c S
  coh h k K := left_coherent D l hl Ω X f c S h k K

private def rightMorphism (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)) :
    (stages l Ω Y).Morphism (stages l Ω X) where
  Φ := finiteRight D l hl Ω X f c S
  β := rightBeta D l hl Ω X f c S
  coh h k K := right_coherent D l hl Ω X f c S h k K

private def unitFamily (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)) :
    StageSystem.Morphism.Hom (StageSystem.Morphism.id (stages l Ω X))
      ((leftMorphism D l hl Ω X f c S).comp (rightMorphism D l hl Ω X f c S)) where
  τ E := (finiteAdjunction D l hl Ω X f c S E).unit
  comm {E L} h K := by
    simp only [StageSystem.Morphism.comp_β_hom_app, StageSystem.Morphism.id_β_hom_app]
    dsimp only [leftMorphism, rightMorphism, leftBeta, rightBeta, Functor.comp_obj,
      StageSystem.Morphism.id, Functor.id_obj]
    erw [Category.id_comp]
    refine adjustBeta_unit (finiteAdjunction D l hl Ω X f c S E)
      (finiteAdjunction D l hl Ω X f c S L)
      (transition_eq l Ω X E L h) (transition_eq l Ω Y E L h)
      (finiteLeftScalar D l hl Ω X f c S E L h)
      (finiteRightScalar D l hl Ω X f c S E L h) ?_ _
    delta GeneralAlgebraicallyClosedCoefficients.stageCategory
    let r := S.fields.rationalComparison c (fieldStage l Ω E) (fieldStage l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
    let := r.shiftX
    let := r.shiftY
    exact r.comparison.unit

private def counitFamily (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)) :
    StageSystem.Morphism.Hom
      ((rightMorphism D l hl Ω X f c S).comp (leftMorphism D l hl Ω X f c S))
      (StageSystem.Morphism.id (stages l Ω Y)) where
  τ E := (finiteAdjunction D l hl Ω X f c S E).counit
  comm {E L} h M := by
    simp only [StageSystem.Morphism.comp_β_hom_app, StageSystem.Morphism.id_β_hom_app]
    dsimp only [leftMorphism, rightMorphism, leftBeta, rightBeta, Functor.comp_obj,
      StageSystem.Morphism.id, Functor.id_obj]
    erw [Category.comp_id]
    symm
    erw [Category.assoc]
    refine adjustBeta_counit (finiteAdjunction D l hl Ω X f c S E)
      (finiteAdjunction D l hl Ω X f c S L)
      (transition_eq l Ω X E L h) (transition_eq l Ω Y E L h)
      (finiteLeftScalar D l hl Ω X f c S E L h)
      (finiteRightScalar D l hl Ω X f c S E L h) ?_ _
    delta GeneralAlgebraicallyClosedCoefficients.stageCategory
    let r := S.fields.rationalComparison c (fieldStage l Ω E) (fieldStage l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
    let := r.shiftX
    let := r.shiftY
    exact r.comparison.counit

private def descendedExceptional (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)) :
    ExceptionalData D l hl Ω X f c where
  system := S
  left := (leftMorphism D l hl Ω X f c S).functor
  right := (rightMorphism D l hl Ω X f c S).functor
  adjunction := StageSystem.Morphism.adjunction
    (leftMorphism D l hl Ω X f c S) (rightMorphism D l hl Ω X f c S)
    (finiteAdjunction D l hl Ω X f c S)
    (unitFamily D l hl Ω X f c S) (counitFamily D l hl Ω X f c S)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  leftComparison E := ((leftMorphism D l hl Ω X f c S).ιCompFunctorIso E).symm
  rightComparison E := ((rightMorphism D l hl Ω X f c S).ιCompFunctorIso E).symm

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
private theorem descendedExceptional_properties (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)) :
    ExceptionalProperties D l hl Ω X f c (descendedExceptional D l hl Ω X f c S) := by
  refine ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ HEq.rfl,
    fun _ _ ↦ HEq.rfl, ?_, ?_, ?_, ?_⟩
  · intro E K
    simp only [descendedExceptional, Iso.symm_hom,
      StageSystem.Morphism.ιCompFunctorIso_inv_app]
    dsimp only [Functor.comp_obj, leftMorphism, rightMorphism, StageSystem.ι]
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
    exact (StageSystem.Morphism.adjunction_unit_app _ _ _ _ _ _ _ _).symm
  · intro E M
    simp only [descendedExceptional, Iso.symm_hom,
      StageSystem.Morphism.ιCompFunctorIso_inv_app]
    dsimp only [Functor.comp_obj, leftMorphism, rightMorphism, StageSystem.ι]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
    exact StageSystem.Morphism.adjunction_counit_app _ _ _ _ _ _ _ _
  · intro E L h K
    simp only [descendedExceptional, Iso.symm_hom,
      StageSystem.Morphism.ιCompFunctorIso_inv_app]
    dsimp only [Functor.comp_obj, leftMorphism, rightMorphism, StageSystem.ι]
    erw [Category.comp_id, Category.id_comp]
    exact adjusted_scalar_square (leftMorphism D l hl Ω X f c S) h
      (transition_eq l Ω X E L h) (transition_eq l Ω Y E L h)
      (finiteLeftScalar D l hl Ω X f c S E L h) rfl K
  · intro E L h M
    simp only [descendedExceptional, Iso.symm_hom,
      StageSystem.Morphism.ιCompFunctorIso_inv_app]
    dsimp only [Functor.comp_obj, leftMorphism, rightMorphism, StageSystem.ι]
    erw [Category.comp_id, Category.id_comp]
    exact adjusted_scalar_square (rightMorphism D l hl Ω X f c S) h
      (transition_eq l Ω Y E L h) (transition_eq l Ω X E L h)
      (finiteRightScalar D l hl Ω X f c S E L h) rfl M

private def formulaOfFinite (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f) (A : Exceptional D l hl Ω X f c)
    (t : FiniteExceptionalFormula D l hl Ω X f BX BY c A.system) :
    ExceptionalFormula D l hl Ω X f BX BY c A := by
  let H := specifiedExceptionalFormula D l hl Ω X f BX BY
  let e : ∀ E : Index l Ω, inclusion (Y := Y) E ⋙ A.right ≅ inclusion E ⋙ H :=
    fun E ↦ (A.rightComparison E).symm ≪≫ t.comparison E
  have he {E L : Index l Ω} (h : E ≤ L) (M : Stage l Ω Y E) :
      A.right.map (((stages l Ω Y).transIso h).hom.app M) ≫ (e E).hom.app M =
        (e L).hom.app (((stages l Ω Y).T h).obj M) ≫
          H.map (((stages l Ω Y).transIso h).hom.app M) := by
    apply adjust_nat_square (stages l Ω Y) A.right H e h (transition_eq l Ω Y E L h) M
    exact comparison_cube
      ((inclusion L).mapIso ((finiteRightScalar D l hl Ω X f c A.system E L h).app M))
      ((A.rightComparison E).app M)
      ((A.rightComparison L).app ((transition l Ω Y E L h).obj M))
      ((inclusionTransition l Ω X E L h).app
        ((finiteRight D l hl Ω X f c A.system E).obj M))
      (A.right.mapIso ((inclusionTransition l Ω Y E L h).app M))
      (H.mapIso ((inclusionTransition l Ω Y E L h).app M))
      ((t.comparison E).app M) ((t.comparison L).app ((transition l Ω Y E L h).obj M))
      (A.properties.2.2.2.2.2.2.2 E L h M) (t.scalar E L h M)
  refine { comparison := glueStageIso (stages l Ω Y) A.right H e he
           finite := t.finite, normalized := ?_ }
  intro E M
  change _ = (A.rightComparison E).hom.app M ≫
    ((A.rightComparison E).inv.app M ≫ (t.comparison E).hom.app M)
  rw [Iso.hom_inv_id_app_assoc]
  exact t.normalized E M

/-- The actual finite exceptional system descends to an adjunction, and its right
adjoint is the Verdier-pullback-Verdier composite for the specified dualities.
Source: blueprint thm-coef-qbar-verdier, proof steps 6--9
(blueprint: lem-coef-qbar-verdier-exceptional-descent).

Proof: take the exceptional system of RationalOperations at the auxiliary small
closure, using only its finite rational coefficient stages. Its normalized scalar
comparisons obey the tower equations, so they define morphisms of the X and Y
stage systems. The descended functors retain the literal stage. Descend the unit
and counit as compatible natural transformations; their compatibility is the mate
condition on the finite scalar comparisons. StageSystem.Morphism.adjunction gives
the adjunction, with its finite components and triangles, and hence all the unit,
counit and scalar equations in ExceptionalProperties. At each finite stage the
normalized internal-Hom descriptions identify the specified BX and BY rational
dualities with those of RationalOperations: uniqueness of the evaluation transpose
fixes these identifications. Transport its finite exceptional comparison through
these identifications. The resulting comparison and inverse obey the scalar tower
squares, so natural-transformation descent identifies the actual descended right
adjoint with BY.dual.rightOp, pullback.op, BX.dual. The finite pullback object formula
and the two duality comparisons give exactly ExceptionalFormula.normalized.
Identity extensions and zero objects are included in the same finite equations. -/
theorem exceptional_descent (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f) :
    ∃ A : Exceptional D l hl Ω X f c,
      Nonempty (ExceptionalFormula D l hl Ω X f BX BY c A) := by
  obtain ⟨S⟩ := ConstructibleExceptionalCoefficients.exists_system
    l (AuxiliaryClosure.{u} l) D hl f
  let A : Exceptional D l hl Ω X f c :=
    ⟨descendedExceptional D l hl Ω X f c S, descendedExceptional_properties D l hl Ω X f c S⟩
  obtain ⟨t⟩ := finite_exceptional_formula D l hl Ω X f BX BY c A.system
  exact ⟨A, ⟨formulaOfFinite D l hl Ω X f BX BY c A t⟩⟩

end WeilConjectures.CoefQbarVerdier
