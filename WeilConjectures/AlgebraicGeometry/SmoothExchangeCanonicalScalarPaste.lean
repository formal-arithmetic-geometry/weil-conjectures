/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothExchangeCanonicalMaps

/-! # Pasting the canonical scalar squares of smooth exchange

Source: smooth purity transport, base-change coefficient coherence.
(blueprint: lem-pur-smooth-exchange-canonical-scalar-paste).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.SmoothExchangeScalarCompatibility
open AdicPurityScalarNaturality RationalScalarComparisonIdentification
attribute [local irreducible] rationalDerivedTensor rationalDerivedPullback
  sfRationalScalarExtension gamma middleFunctor
  ScalarLocalization.composition sfIntegralConstructible sfIntegralConstructibleLinear
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory AlgebraicGeometry.Scheme.residueField
  ScalarLocalization.category
attribute [local semireducible] b
attribute [local implicit_reducible] A B H T G O b
  ConstructibleExceptionalCoefficients.category
  AdicPurityScalarNaturality.fieldStage ConstructibleExceptionalCoefficients.FieldComparison.b

private theorem inversePullScalarSquare
    {X₀ X₁ Y₀ Y₁ : Type*} [Category X₀] [Category X₁] [Category Y₀] [Category Y₁]
    (P : X₀ ⥤ Y₀) (P' : X₁ ⥤ Y₁) (TX : X₀ ⥤ X₁) (TY : Y₀ ⥤ Y₁)
    (p : P ⋙ TY ≅ TX ⋙ P') {A₀ B₀ : X₀} {A₁ B₁ : X₁}
    (e : A₀ ≅ B₀) (e' : A₁ ≅ B₁) (a : TX.obj A₀ ≅ A₁) (b : TX.obj B₀ ≅ B₁)
    (h : TX.map e.inv ≫ a.hom = b.hom ≫ e'.inv) :
    TY.map (P.map e.inv) ≫ p.hom.app A₀ ≫ P'.map a.hom =
      (p.hom.app B₀ ≫ P'.map b.hom) ≫ P'.map e'.inv := by
  have hp := p.hom.naturality e.inv
  change TY.map (P.map e.inv) ≫ p.hom.app A₀ =
    p.hom.app B₀ ≫ P'.map (TX.map e.inv) at hp
  rw [← Category.assoc, hp, Category.assoc, ← P'.map_comp, h, P'.map_comp]
  simp only [Category.assoc]

private theorem threeFactorScalar
    {A₀ A₁ : Type*} [Category A₀] [Category A₁] (T : A₀ ⥤ A₁)
    {W X Y Z : A₀} {W' X' Y' Z' : A₁}
    {s : W ⟶ X} (m : X ⟶ Y) {t : Y ⟶ Z}
    {s' : W' ⟶ X'} (m' : X' ⟶ Y') {t' : Y' ⟶ Z'}
    {bA : T.obj W ⟶ W'} {a : T.obj X ⟶ X'}
    {b : T.obj Y ⟶ Y'} {bB : T.obj Z ⟶ Z'}
    (hs : T.map s ≫ a = bA ≫ s') (hm : T.map m ≫ b = a ≫ m')
    (ht : T.map t ≫ bB = b ≫ t') :
    T.map (s ≫ m ≫ t) ≫ bB = bA ≫ s' ≫ m' ≫ t' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [ht, reassoc_of% hm, reassoc_of% hs]

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

section Arrow
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
/-- The exceptional scalar comparison has the recorded coefficient unit law.
Source: the supplied system's rational identity comparison
(blueprint: lem-pur-smooth-exchange-canonical-scalar-paste). -/
theorem b_unit (E : AdicPurityScalarNaturality.Field D C) :
    UnitEquation (b D C f S E E le_rfl) (unit D C E X) (unit D C E Y) := by
  intro K
  unfold b
  exact S.fields.rationalIdentityRight (integralExceptionalCompactification D f)
    (fieldStage D C E) K

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
/-- The exceptional scalar comparisons have the recorded coefficient tower law.
Source: the supplied system's rational cocycle
(blueprint: lem-pur-smooth-exchange-canonical-scalar-paste). -/
theorem b_tower (E F L : AdicPurityScalarNaturality.Field D C)
    (h : E ≤ F) (k : F ≤ L) :
    CompositionEquation (b D C f S E F h) (b D C f S F L k)
      (b D C f S E L (h.trans k)) (alpha D C E F L h k X)
      (alpha D C E F L h k Y) := by
  intro K
  have hc := S.fields.rationalCocycle (integralExceptionalCompactification D f)
    (fieldStage D C E) (fieldStage D C F) (fieldStage D C L)
    (IntermediateField.inclusion h) (IntermediateField.inclusion k)
  rcases hc with ⟨_, hr⟩
  have hh := (hr K).symm
  dsimp only [CompositionEquation, b, alpha, T, G, O,
    ConstructibleExceptionalCoefficients.FieldComparison.b,
    ConstructibleExceptionalCoefficients.rationalScalar, fieldStage,
    IntermediateField.inclusion, Subalgebra.inclusion, AlgHom.comp, RingHom.comp,
    Set.inclusion, Functor.comp_obj] at hh ⊢
  exact hh

end Arrow

section Square
variable {X X' Y Y' : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [X'.Over (Spec (.of D.k))]
  [Y.Over (Spec (.of D.k))] [Y'.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of D.k))] [QuasiCompact (X' ↘ Spec (.of D.k))]
  [IsSeparated (X' ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))] [QuasiCompact (Y' ↘ Spec (.of D.k))]
  [IsSeparated (Y' ↘ Spec (.of D.k))]
  (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
  [u.IsOver (Spec (.of D.k))] [f.IsOver (Spec (.of D.k))]
  [f'.IsOver (Spec (.of D.k))] [v.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (S' : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f'))

omit [u.IsOver (Spec (.of D.k))] [v.IsOver (Spec (.of D.k))] in
/-- Natural purity families assemble the specified component exchange into a natural
isomorphism. The purity components are required to be the actual canonical gamma;
no replacement of the exchange map or extra finite-right normalization occurs.
Source: smooth purity transport, base-change coherence by conjugation
(blueprint: lem-pur-smooth-exchange-canonical-scalar-paste). -/
theorem exchangeFunctor_of_purity (sq : u ≫ f = f' ≫ v) (d : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    (E : AdicPurityScalarNaturality.Field D C)
    (η : H D C f d E ≅ G D C f S E)
    (η' : H D C f' d E ≅ G D C f' S' E)
    (hη : ∀ K : RCat D C E Y, η.app K = gamma D C f S d E K)
    (hη' : ∀ K : RCat D C E Y', η'.app K = gamma D C f' S' d E K) :
    ∃ e : A D C u f S E ≅ B D C f' v S' E,
      ∀ K : RCat D C E Y, e.app K = exchange D C u f f' v S S' sq d E K := by
  refine ⟨isoWhiskerRight η.symm (rationalDerivedPullback C.l E.val u) ≪≫
    middleFunctor D C u f f' v sq d E ≪≫
      isoWhiskerLeft (rationalDerivedPullback C.l E.val v) η', ?_⟩
  intro K
  change (rationalDerivedPullback C.l E.val u).mapIso (η.app K).symm ≪≫
      (middleFunctor D C u f f' v sq d E).app K ≪≫
      η'.app ((rationalDerivedPullback C.l E.val v).obj K) = _
  rw [hη K, hη' _]
  simp only [exchange, middle]


omit [u.IsOver (Spec (.of D.k))] [v.IsOver (Spec (.of D.k))] in
/-- The canonical source scalar comparisons suffice for the actual exchange square.
The remaining assumptions are precisely the middle scalar square and naturality of
forward purity at the pullback scalar map. Neither asks for normalized finite-right
realizations of the supplied systems.
Source: smooth purity transport, pasting the inverse-purity, middle, and purity squares
(blueprint: lem-pur-smooth-exchange-canonical-scalar-paste). -/
theorem exchange_scalar_of_middle (sq : u ≫ f = f' ≫ v) (d : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) (K : RCat D C E Y)
    (hm : (T D C E L h X').map (middle D C u f f' v sq d E K).hom ≫
        (RationalSmoothPurityCanonical.sourceScalar C.l E.val L.val
          (IntermediateField.inclusion h) f' d
          ((rationalDerivedPullback C.l E.val v).obj K)).hom ≫
        (H D C f' d L).map
          ((rationalPullbackScalarComparison C.l E.val L.val
            (IntermediateField.inclusion h) v).hom.app K) =
      (rationalPullbackScalarComparison C.l E.val L.val
        (IntermediateField.inclusion h) u).hom.app ((H D C f d E).obj K) ≫
        (rationalDerivedPullback C.l L.val u).map
          (RationalSmoothPurityCanonical.sourceScalar C.l E.val L.val
            (IntermediateField.inclusion h) f d K).hom ≫
        (middle D C u f f' v sq d L ((T D C E L h Y).obj K)).hom)
    (hn : (H D C f' d L).map
        ((rationalPullbackScalarComparison C.l E.val L.val
          (IntermediateField.inclusion h) v).hom.app K) ≫
        (gamma D C f' S' d L
          ((rationalDerivedPullback C.l L.val v).obj ((T D C E L h Y).obj K))).hom =
      (gamma D C f' S' d L
        ((T D C E L h Y').obj ((rationalDerivedPullback C.l E.val v).obj K))).hom ≫
        (G D C f' S' L).map
          ((rationalPullbackScalarComparison C.l E.val L.val
            (IntermediateField.inclusion h) v).hom.app K)) :
    (T D C E L h X').map (exchange D C u f f' v S S' sq d E K).hom ≫
        (betaB D C f' v S' E L h).hom.app K =
      (betaA D C u f S E L h).hom.app K ≫
        (exchange D C u f f' v S S' sq d L ((T D C E L h Y).obj K)).hom := by
  dsimp only [T, H] at hm hn ⊢
  let pU := rationalPullbackScalarComparison C.l E.val L.val
    (IntermediateField.inclusion h) u
  let pV := rationalPullbackScalarComparison C.l E.val L.val
    (IntermediateField.inclusion h) v
  let a := RationalSmoothPurityCanonical.sourceScalar C.l E.val L.val
    (IntermediateField.inclusion h) f d K
  let a' := RationalSmoothPurityCanonical.sourceScalar C.l E.val L.val
    (IntermediateField.inclusion h) f' d ((rationalDerivedPullback C.l E.val v).obj K)
  have hs : (T D C E L h X').map
        ((rationalDerivedPullback C.l E.val u).map (gamma D C f S d E K).inv) ≫
        pU.hom.app ((H D C f d E).obj K) ≫
        (rationalDerivedPullback C.l L.val u).map a.hom =
      (betaA D C u f S E L h).hom.app K ≫
        (rationalDerivedPullback C.l L.val u).map
          (gamma D C f S d L ((T D C E L h Y).obj K)).inv := by
    have hs := inversePullScalarSquare
      (rationalDerivedPullback C.l E.val u) (rationalDerivedPullback C.l L.val u)
      (T D C E L h X) (T D C E L h X') pU
      (gamma D C f S d E K) (gamma D C f S d L ((T D C E L h Y).obj K))
      a ((b D C f S E L h).app K) (gamma_scalar_inv D C f S d E L h K)
    simpa only [betaA, A, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
      Category.comp_id, Category.assoc, pU, T, H, Iso.app_hom] using hs
  have ht : (T D C E L h X').map
        (gamma D C f' S' d E ((rationalDerivedPullback C.l E.val v).obj K)).hom ≫
        (betaB D C f' v S' E L h).hom.app K =
      a'.hom ≫ (H D C f' d L).map (pV.hom.app K) ≫
        (gamma D C f' S' d L
          ((rationalDerivedPullback C.l L.val v).obj ((T D C E L h Y).obj K))).hom := by
    simp only [betaB, B, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
      Category.comp_id, Functor.comp_obj, T, H]
    have ht₀ := gamma_scalar D C f' S' d E L h
      ((rationalDerivedPullback C.l E.val v).obj K)
    dsimp only [T, H] at ht₀
    calc
      _ = (a'.hom ≫ (gamma D C f' S' d L
          ((T D C E L h Y').obj ((rationalDerivedPullback C.l E.val v).obj K))).hom) ≫
          (G D C f' S' L).map (pV.hom.app K) := by
        simpa only [Category.assoc, a', pV, T] using
          congrArg (fun z ↦ z ≫ (G D C f' S' L).map (pV.hom.app K)) ht₀
      _ = _ := by
        simpa only [Category.assoc, pV, T] using congrArg (fun z ↦ a'.hom ≫ z) hn.symm
  have hp := threeFactorScalar (T D C E L h X')
    (s := ((rationalDerivedPullback C.l E.val u).map (gamma D C f S d E K).inv))
    (m := (middle D C u f f' v sq d E K).hom)
    (t := (gamma D C f' S' d E ((rationalDerivedPullback C.l E.val v).obj K)).hom)
    (s' := ((rationalDerivedPullback C.l L.val u).map
      (gamma D C f S d L ((T D C E L h Y).obj K)).inv))
    (m' := (middle D C u f f' v sq d L ((T D C E L h Y).obj K)).hom)
    (t' := (gamma D C f' S' d L
      ((rationalDerivedPullback C.l L.val v).obj ((T D C E L h Y).obj K))).hom)
    (bA := (betaA D C u f S E L h).hom.app K)
    (a := pU.hom.app ((H D C f d E).obj K) ≫
      (rationalDerivedPullback C.l L.val u).map a.hom)
    (b := a'.hom ≫ (H D C f' d L).map (pV.hom.app K))
    (bB := (betaB D C f' v S' E L h).hom.app K)
    hs (by simpa only [Category.assoc, pU, a, T, H] using hm)
      (by simpa only [Category.assoc] using ht)
  simpa only [exchange, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, T, H] using hp


end Square
end WeilConjectures.SmoothExchangeScalarCompatibility
