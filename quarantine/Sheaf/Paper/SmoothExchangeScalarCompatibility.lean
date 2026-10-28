/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.RationalSmoothPurityCanonical
public import Sheaf.Paper.RationalScalarComparisonData
public import Sheaf.Paper.TwistedPullbackSquareScalars
public import Sheaf.Paper.RationalPurityExchangeEndpoints
public import Sheaf.Paper.RationalPurityExchangeEndpointData
import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Scalar compatibility of the actual smooth purity exchange

Source: current blueprint sec-smooth-purity/sk-thm-purity-transport,
coefficient-change and base-change coherence
(blueprint: lem-pur-smooth-exchange-scalar-compatibility).

The shifted Tate line is placed first, as in the published canonical rational purity.
The middle arrow is pullback of tensor, pullback of the shifted root line, and the
ordinary pullback square. All three factors have specified constructions.
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
  sfRationalScalarExtension

/-- Three commuting scalar squares paste in the functor category.
Source: elementary natural-transformation composition
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
private theorem pasteScalar
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁]
    {A₀ H₀ J₀ B₀ : C₀ ⥤ D₀} {A₁ H₁ J₁ B₁ : C₁ ⥤ D₁}
    (T : C₀ ⥤ C₁) (U : D₀ ⥤ D₁)
    (s : A₀ ≅ H₀) (m : H₀ ≅ J₀) (t : J₀ ≅ B₀)
    (s' : A₁ ≅ H₁) (m' : H₁ ≅ J₁) (t' : J₁ ≅ B₁)
    (aA : A₀ ⋙ U ≅ T ⋙ A₁) (aH : H₀ ⋙ U ≅ T ⋙ H₁)
    (aJ : J₀ ⋙ U ≅ T ⋙ J₁) (aB : B₀ ⋙ U ≅ T ⋙ B₁)
    (hs : whiskerRight s.hom U ≫ aH.hom = aA.hom ≫ whiskerLeft T s'.hom)
    (hm : whiskerRight m.hom U ≫ aJ.hom = aH.hom ≫ whiskerLeft T m'.hom)
    (ht : whiskerRight t.hom U ≫ aB.hom = aJ.hom ≫ whiskerLeft T t'.hom) :
    whiskerRight (s ≪≫ m ≪≫ t).hom U ≫ aB.hom =
      aA.hom ≫ whiskerLeft T (s' ≪≫ m' ≪≫ t').hom := by
  simp only [Iso.trans_hom, whiskerRight_comp, whiskerLeft_comp, Category.assoc]
  rw [ht, reassoc_of% hm, reassoc_of% hs]

/-- A natural tensor comparison followed by a fixed line map and a natural square.
Source: elementary naturality under a bifunctor
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
theorem tensorMiddle_naturality
    {A₀ D₀ D₁ : Type*} [Category* A₀] [Category* D₀] [Category* D₁]
    (F : A₀ ⥤ D₀) (P : D₀ ⥤ D₁) (TX : D₀ × D₀ ⥤ D₀)
    (TX' : D₁ × D₁ ⥤ D₁) (β : TX ⋙ P ≅ P.prod P ⋙ TX')
    (c : ∀ M N : D₀, P.obj (TX.obj (M, N)) ≅ TX'.obj (P.obj M, P.obj N))
    (hc : ∀ M N, β.app (M, N) = c M N)
    (L : D₀) (L' : D₁) (z : P.obj L ≅ L')
    (J : A₀ ⥤ D₁) (t : F ⋙ P ≅ J) {K N : A₀} (a : K ⟶ N) :
    P.map (TX.map (Prod.mkHom (𝟙 L) (F.map a))) ≫
        ((c L (F.obj N)).hom ≫ TX'.map (Prod.mkHom z.hom (t.hom.app N))) =
      ((c L (F.obj K)).hom ≫ TX'.map (Prod.mkHom z.hom (t.hom.app K))) ≫
        TX'.map (Prod.mkHom (𝟙 L') (J.map a)) := by
  have h := β.hom.naturality (Prod.mkHom (𝟙 L) (F.map a))
  change P.map (TX.map (Prod.mkHom (𝟙 L) (F.map a))) ≫ (β.app (L, F.obj N)).hom =
    (β.app (L, F.obj K)).hom ≫
      TX'.map (Prod.mkHom (P.map (𝟙 L)) (P.map (F.map a))) at h
  rw [hc L (F.obj N), hc L (F.obj K), P.map_id] at h
  have hn : TX'.map (Prod.mkHom (𝟙 _) (P.map (F.map a))) ≫
        TX'.map (Prod.mkHom z.hom (t.hom.app N)) =
      TX'.map (Prod.mkHom z.hom (t.hom.app K)) ≫
        TX'.map (Prod.mkHom (𝟙 L') (J.map a)) := by
    rw [← TX'.map_comp, ← TX'.map_comp]
    apply congrArg TX'.map
    ext
    · simp
    · exact t.hom.naturality a
  rw [← Category.assoc, h, Category.assoc, hn, ← Category.assoc]

/-- The tensor comparison and an ordinary pullback square give a natural middle map.
Source: naturality under the tensor bifunctor
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def tensorExchangeIso
    {A₀ A₁ D₀ D₁ : Type*} [Category* A₀] [Category* A₁]
    [Category* D₀] [Category* D₁]
    (F : A₀ ⥤ D₀) (P : D₀ ⥤ D₁) (TX : D₀ × D₀ ⥤ D₀)
    (TX' : D₁ × D₁ ⥤ D₁) (β : TX ⋙ P ≅ P.prod P ⋙ TX')
    (c : ∀ M N : D₀, P.obj (TX.obj (M, N)) ≅ TX'.obj (P.obj M, P.obj N))
    (hc : ∀ M N, β.app (M, N) = c M N)
    (L : D₀) (L' : D₁) (z : P.obj L ≅ L')
    (V : A₀ ⥤ A₁) (F' : A₁ ⥤ D₁) (t : F ⋙ P ≅ V ⋙ F') :
    (((Functor.const A₀).obj L).prod' F ⋙ TX) ⋙ P ≅
      V ⋙ (((Functor.const A₁).obj L').prod' F' ⋙ TX') :=
  NatIso.ofComponents
    (fun K ↦ c L (F.obj K) ≪≫ TX'.mapIso (Iso.prod z (t.app K)))
    (fun a ↦ by
      simpa only [Functor.comp_map, Functor.prod'_map, Functor.const_obj_map,
        Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom] using
        tensorMiddle_naturality F P TX TX' β c hc L L' z (V ⋙ F') t a)

/-- Components of the abstract functor-category construction.
Source: the definition of tensorExchangeIso
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
theorem tensorExchangeIso_app
    {A₀ A₁ D₀ D₁ : Type*} [Category* A₀] [Category* A₁]
    [Category* D₀] [Category* D₁]
    (F : A₀ ⥤ D₀) (P : D₀ ⥤ D₁) (TX : D₀ × D₀ ⥤ D₀)
    (TX' : D₁ × D₁ ⥤ D₁) (β : TX ⋙ P ≅ P.prod P ⋙ TX')
    (c : ∀ M N : D₀, P.obj (TX.obj (M, N)) ≅ TX'.obj (P.obj M, P.obj N))
    (hc : ∀ M N, β.app (M, N) = c M N)
    (L : D₀) (L' : D₁) (z : P.obj L ≅ L')
    (V : A₀ ⥤ A₁) (F' : A₁ ⥤ D₁) (t : F ⋙ P ≅ V ⋙ F') (K : A₀) :
    (tensorExchangeIso F P TX TX' β c hc L L' z V F' t).app K =
      c L (F.obj K) ≪≫ TX'.mapIso (Iso.prod z (t.app K)) :=
  NatIso.ofComponents.app _ _ K

attribute [local irreducible] tensorExchangeIso

/-- Three shift-compatible natural isomorphisms have a shift-compatible composite.
Source: elementary composition of the three shift equations
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
private theorem pasteShift {A₀ D₀ : Type*} [Category* A₀] [Category* D₀]
    [HasShift A₀ ℤ] [HasShift D₀ ℤ] {F₀ F₁ F₂ F₃ : A₀ ⥤ D₀}
    [F₀.CommShift ℤ] [F₁.CommShift ℤ] [F₂.CommShift ℤ] [F₃.CommShift ℤ]
    (s : F₀ ≅ F₁) (m : F₁ ≅ F₂) (t : F₂ ≅ F₃)
    (hs : NatTrans.CommShift s.hom ℤ) (hm : NatTrans.CommShift m.hom ℤ)
    (ht : NatTrans.CommShift t.hom ℤ) : NatTrans.CommShift (s ≪≫ m ≪≫ t).hom ℤ := by
  change NatTrans.CommShift (s.hom ≫ m.hom ≫ t.hom) ℤ
  refine ⟨fun n ↦ ?_⟩
  simp only [whiskerRight_comp, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% (hs.shift_comm n), reassoc_of% (hm.shift_comm n), ht.shift_comm n]

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

/-- The existing purity setting at E; level one is only unused finite-level bookkeeping.
Source: purity coefficient conventions
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
abbrev setting (E : AdicPurityScalarNaturality.Field D C) : PurityFiniteSetting.{u} :=
  { field := D, coefficients := C, extension := E.val, level := 1, level_pos := le_rfl }

/-- The normalized tensor comparison is uniquely determined by its components.
Source: the rational clause of the derived pullback/tensor theorem and extensionality
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
theorem tensorComparisonUnique (E : AdicPurityScalarNaturality.Field D C)
    {U V : Scheme.{u}} (u : U ⟶ V)
    [∀ x : U, Invertible (C.l : U.residueField x)]
    [∀ x : V, Invertible (C.l : V.residueField x)] :
    ∃! β : rationalDerivedTensor C.l E.val V ⋙ rationalDerivedPullback C.l E.val u ≅
        (rationalDerivedPullback C.l E.val u).prod
          (rationalDerivedPullback C.l E.val u) ⋙ rationalDerivedTensor C.l E.val U,
      ∀ M N, β.app (M, N) = canonicalRationalPullbackTensor C.l E.val u M N := by
  obtain ⟨β, hβ⟩ := (derivedPullbackTensorIso C.l E.val u 0 C.Qbar).2.2.2.2.2.2.1
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  apply Iso.ext
  apply NatTrans.ext
  funext p
  exact congrArg Iso.hom ((hγ p.1 p.2).trans (hβ p.1 p.2).symm)


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

/-- The published rationalization of the finite-trace-normalized integral purity map.
Source: rational purity and coefficient change, rationalization clause
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def gamma (d : ℕ) [SmoothOfRelativeDimension d f]
    (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y) :
    (H D C f d E).obj K ≅ (G D C f S E).obj K := by
  simpa only [H, G, O, AdicPurityScalarNaturality.fieldStage] using
    RationalSmoothPurityCanonical.rationalIso (setting D C E) f
      (integralExceptionalCompactification D f) S d K

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

/-- Domain of the smooth exchange. Source: purity base-change coherence
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def A (E : AdicPurityScalarNaturality.Field D C) :=
  G D C f S E ⋙ rationalDerivedPullback C.l E.val u

/-- Codomain of the smooth exchange. Source: purity base-change coherence
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def B (E : AdicPurityScalarNaturality.Field D C) :=
  rationalDerivedPullback C.l E.val v ⋙ G D C f' S' E

/-- The canonical middle comparison, constructed in the functor category.
The uniquely specified tensor comparison is determined by all its components; no
arbitrary tensor comparison is selected. Source: smooth-purity pullback coherence
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def middleFunctor (sq : u ≫ f = f' ≫ v) (d : ℕ)
    (E : AdicPurityScalarNaturality.Field D C) :
    H D C f d E ⋙ rationalDerivedPullback C.l E.val u ≅
      rationalDerivedPullback C.l E.val v ⋙ H D C f' d E := by
  dsimp only [H, RationalSmoothPurityCanonical.rationalSource]
  exact tensorExchangeIso (rationalDerivedPullback C.l E.val f)
    (rationalDerivedPullback C.l E.val u) (rationalDerivedTensor C.l E.val X)
    (rationalDerivedTensor C.l E.val X') (tensorComparisonUnique D C E u).exists.choose
    (canonicalRationalPullbackTensor C.l E.val u)
    (tensorComparisonUnique D C E u).exists.choose_spec
    ((sfRationalTwistingCoefficient C.l E.val X (d : ℤ))⟦2 * (d : ℤ)⟧)
    ((sfRationalTwistingCoefficient C.l E.val X' (d : ℤ))⟦2 * (d : ℤ)⟧)
    (((rationalDerivedPullback C.l E.val u).commShiftIso (2 * (d : ℤ))).app _ ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso (CanonicalTate.rationalPull C.l E.val u d))
    (rationalDerivedPullback C.l E.val v) (rationalDerivedPullback C.l E.val f')
    (TwistedPullbackScalars.t C.l E.val u f f' v sq)

/-- The actual middle comparison in the shifted-line-first purity coordinates.
Source: the finite smooth pullback exchange, reconstructed and rationalized
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def middle (sq : u ≫ f = f' ≫ v) (d : ℕ)
    (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y) :
    (rationalDerivedPullback C.l E.val u).obj ((H D C f d E).obj K) ≅
      (H D C f' d E).obj ((rationalDerivedPullback C.l E.val v).obj K) :=
  (middleFunctor D C u f f' v sq d E).app K

attribute [local implicit_reducible] TwistedPullbackScalars.U TwistedPullbackScalars.V
  H RationalSmoothPurityCanonical.rationalSource

omit
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of D.k))]
  [QuasiCompact (X' ↘ Spec (.of D.k))]
  [IsSeparated (X' ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))]
  [QuasiCompact (Y' ↘ Spec (.of D.k))]
  [IsSeparated (Y' ↘ Spec (.of D.k))]
  [u.IsOver (Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))]
  [f'.IsOver (Spec (.of D.k))]
  [v.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f'] in
/-- The functor-category construction has exactly the original canonical component.
Source: the component normalization of the tensor comparison
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
theorem middle_component (sq : u ≫ f = f' ≫ v) (d : ℕ)
    (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y) :
    middle D C u f f' v sq d E K =
      canonicalRationalPullbackTensor C.l E.val u
        ((sfRationalTwistingCoefficient C.l E.val X (d : ℤ))⟦2 * (d : ℤ)⟧)
        ((rationalDerivedPullback C.l E.val f).obj K) ≪≫
      (rationalDerivedTensor C.l E.val X').mapIso
        (Iso.prod
          (((rationalDerivedPullback C.l E.val u).commShiftIso (2 * (d : ℤ))).app _ ≪≫
            (shiftFunctor _ (2 * (d : ℤ))).mapIso
              (CanonicalTate.rationalPull C.l E.val u d))
          ((TwistedPullbackScalars.t C.l E.val u f f' v sq).app K)) := by
  dsimp only [middle, middleFunctor, _root_.id]
  rw [tensorExchangeIso_app]

attribute [local irreducible] middleFunctor

/-- The actual inverse-purity / pullback-square / purity exchange, with no free map.
Source: smooth purity base-change coherence and its coefficient transport
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def exchange (sq : u ≫ f = f' ≫ v) (d : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y) :
    (A D C u f S E).obj K ≅ (B D C f' v S' E).obj K :=
  (rationalDerivedPullback C.l E.val u).mapIso (gamma D C f S d E K).symm ≪≫
    middle D C u f f' v sq d E K ≪≫
    gamma D C f' S' d E ((rationalDerivedPullback C.l E.val v).obj K)

/-- beta_A is p_u followed by pullback of the counit-normalized b_f.
Source: scalar equation of smooth purity exchange
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def betaA (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) :
    A D C u f S E ⋙ T D C E L h X' ≅ T D C E L h Y ⋙ A D C u f S L :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (G D C f S E) (rationalPullbackScalarComparison C.l E.val L.val
      (IntermediateField.inclusion h) u) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (b D C f S E L h) (rationalDerivedPullback C.l L.val u) ≪≫
    Functor.associator _ _ _

/-- beta_B is b_f' followed by exceptional pullback of p_v.
Source: scalar equation of smooth purity exchange
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def betaB (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) :
    B D C f' v S' E ⋙ T D C E L h X' ≅ T D C E L h Y ⋙ B D C f' v S' L :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (rationalDerivedPullback C.l E.val v) (b D C f' S' E L h) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (rationalPullbackScalarComparison C.l E.val L.val
      (IntermediateField.inclusion h) v) (G D C f' S' L) ≪≫
    Functor.associator _ _ _

/-- The endpoint shift structure uses the specified exceptional and pullback shifts.
Source: purity transport, shift identifications
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
@[instance_reducible]
def aShift (E : AdicPurityScalarNaturality.Field D C) : (A D C u f S E).CommShift ℤ :=
  composeShift _ _ (gShift D C f S E) inferInstance

/-- The endpoint shift structure uses the specified pullback and exceptional shifts.
Source: purity transport, shift identifications
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
@[instance_reducible]
def bShift (E : AdicPurityScalarNaturality.Field D C) : (B D C f' v S' E).CommShift ℤ :=
  composeShift _ _ inferInstance (gShift D C f' S' E)

attribute [local irreducible] G O middle ScalarLocalization.composition
  sfIntegralConstructible sfIntegralConstructibleLinear HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.residueField ScalarLocalization.category

omit
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of D.k))]
  [QuasiCompact (X' ↘ Spec (.of D.k))]
  [IsSeparated (X' ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))]
  [QuasiCompact (Y' ↘ Spec (.of D.k))]
  [IsSeparated (Y' ↘ Spec (.of D.k))]
  [u.IsOver (Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))]
  [f'.IsOver (Spec (.of D.k))]
  [v.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f'] in
/-- The specified component is natural because it is a functor-category component.
Source: smooth-purity pullback coherence
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
theorem middle_naturality (sq : u ≫ f = f' ≫ v) (d : ℕ)
    (E : AdicPurityScalarNaturality.Field D C) (K N : RCat D C E Y) (a : K ⟶ N) :
    (H D C f d E ⋙ rationalDerivedPullback C.l E.val u).map a ≫
        (middle D C u f f' v sq d E N).hom =
      (middle D C u f f' v sq d E K).hom ≫
        (rationalDerivedPullback C.l E.val v ⋙ H D C f' d E).map a := by
  unfold middle
  exact (middleFunctor D C u f f' v sq d E).hom.naturality a

attribute [local irreducible] H RationalPurityExchangeEndpoints.comparisonA
  RationalPurityExchangeEndpoints.comparisonB

omit [u.IsOver (Spec (.of D.k))] [v.IsOver (Spec (.of D.k))] in
/-- Paste the normalized endpoint and middle scalar squares, retaining every coefficient law.
This is the assembly in Steps 3–4 of the node's proof. The endpoint and middle data are
explicit hypotheses: the unrestricted System API does not currently construct their
canonical normalization. Source: smooth-purity transport, base-change coefficient coherence
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
private theorem assembleExchange (sq : u ≫ f = f' ≫ v) (d : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    (I : AdicPurityScalarNaturality.Data D C f d S)
    (I' : AdicPurityScalarNaturality.Data D C f' d S')
    (R : RationalPurityExchangeEndpoints.LocalizedFamily D C f d S I)
    (R' : RationalPurityExchangeEndpoints.LocalizedFamily D C f' d S' I')
    (hEnds : RationalPurityExchangeEndpoints.EndpointEquations
      D C u f f' v d S S' I I' R R')
    (hCanonical : ∀ (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y),
      (R.gamma E).app K = gamma D C f S d E K)
    (hCanonical' : ∀ (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y'),
      (R'.gamma E).app K = gamma D C f' S' d E K)
    (m : ∀ E : AdicPurityScalarNaturality.Field D C,
      RationalPurityExchangeEndpoints.endpointA D C u f d S E false ≅
        RationalPurityExchangeEndpoints.endpointB D C f' v d S' E false)
    (hm : ∀ (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y),
      (m E).app K = middle D C u f f' v sq d E K)
    (hScalar : ∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
      whiskerRight (m E).hom (T D C E L h X') ≫
          (RationalPurityExchangeEndpoints.comparisonB D C f' v d S' I' R' E L h false).hom =
        (RationalPurityExchangeEndpoints.comparisonA D C u f d S I R E L h false).hom ≫
          whiskerLeft (T D C E L h Y) (m L).hom)
    (hShift : ∀ E : AdicPurityScalarNaturality.Field D C,
      ShiftCompatibility (RationalPurityExchangeEndpoints.endpointA D C u f d S E false)
        (RationalPurityExchangeEndpoints.endpointB D C f' v d S' E false)
        (RationalPurityExchangeEndpoints.shiftA D C u f d S I R E false)
        (RationalPurityExchangeEndpoints.shiftB D C f' v d S' I' R' E false) (m E)) :
  ∃ e : ∀ E : AdicPurityScalarNaturality.Field D C, A D C u f S E ≅ B D C f' v S' E,
    (∀ (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y),
      (e E).app K = exchange D C u f f' v S S' sq d E K) ∧
    (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
      whiskerRight (e E).hom (T D C E L h X') ≫ (betaB D C f' v S' E L h).hom =
        (betaA D C u f S E L h).hom ≫ whiskerLeft (T D C E L h Y) (e L).hom) ∧
    (∀ E : AdicPurityScalarNaturality.Field D C,
      UnitEquation (betaA D C u f S E E le_rfl) (unit D C E X') (unit D C E Y) ∧
      UnitEquation (betaB D C f' v S' E E le_rfl) (unit D C E X') (unit D C E Y)) ∧
    (∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
      CompositionEquation (betaA D C u f S E F h) (betaA D C u f S F L k)
        (betaA D C u f S E L (h.trans k)) (alpha D C E F L h k X')
        (alpha D C E F L h k Y) ∧
      CompositionEquation (betaB D C f' v S' E F h) (betaB D C f' v S' F L k)
        (betaB D C f' v S' E L (h.trans k)) (alpha D C E F L h k X')
        (alpha D C E F L h k Y)) ∧
    (∀ E : AdicPurityScalarNaturality.Field D C,
      ShiftCompatibility (A D C u f S E) (B D C f' v S' E)
        (aShift D C u f S E) (bShift D C f' v S' E) (e E)) ∧
    (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
      ShiftCompatibility (A D C u f S E ⋙ T D C E L h X')
        (T D C E L h Y ⋙ A D C u f S L)
        (composeShift _ _ (aShift D C u f S E) (tShift D C E L h X'))
        (composeShift _ _ (tShift D C E L h Y) (aShift D C u f S L))
        (betaA D C u f S E L h) ∧
      ShiftCompatibility (B D C f' v S' E ⋙ T D C E L h X')
        (T D C E L h Y ⋙ B D C f' v S' L)
        (composeShift _ _ (bShift D C f' v S' E) (tShift D C E L h X'))
        (composeShift _ _ (tShift D C E L h Y) (bShift D C f' v S' L))
        (betaB D C f' v S' E L h)) := by
  let s (E : AdicPurityScalarNaturality.Field D C) :
      A D C u f S E ≅ H D C f d E ⋙ rationalDerivedPullback C.l E.val u :=
    RationalPurityExchangeEndpoints.s D C u f d S I R E
  let t (E : AdicPurityScalarNaturality.Field D C) :
      rationalDerivedPullback C.l E.val v ⋙ H D C f' d E ≅ B D C f' v S' E :=
    RationalPurityExchangeEndpoints.tGamma D C f' v d S' I' R' E
  let mid (E : AdicPurityScalarNaturality.Field D C) :
      H D C f d E ⋙ rationalDerivedPullback C.l E.val u ≅
        rationalDerivedPullback C.l E.val v ⋙ H D C f' d E := m E
  let e (E : AdicPurityScalarNaturality.Field D C) :
      A D C u f S E ≅ B D C f' v S' E := s E ≪≫ mid E ≪≫ t E
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro E K
    change (rationalDerivedPullback C.l E.val u).mapIso ((R.gamma E).app K).symm ≪≫
      (m E).app K ≪≫
      (R'.gamma E).app ((rationalDerivedPullback C.l E.val v).obj K) = _
    rw [hCanonical E K, hCanonical' E _, hm E K]
    rfl
  · intro E L h
    have ha := hEnds.squareA E L h
    have hb := hEnds.squareB E L h
    have hm' := hScalar E L h
    change whiskerRight (s E).hom _ ≫ _ = _ ≫ whiskerLeft _ (s L).hom at ha
    change whiskerRight (t E).hom _ ≫ _ = _ ≫ whiskerLeft _ (t L).hom at hb
    change whiskerRight (mid E).hom _ ≫ _ = _ ≫ whiskerLeft _ (mid L).hom at hm'
    have hp := pasteScalar (T D C E L h Y) (T D C E L h X')
      (s E) (mid E) (t E) (s L) (mid L) (t L)
      (RationalPurityExchangeEndpoints.comparisonA D C u f d S I R E L h true)
      (RationalPurityExchangeEndpoints.comparisonA D C u f d S I R E L h false)
      (RationalPurityExchangeEndpoints.comparisonB D C f' v d S' I' R' E L h false)
      (RationalPurityExchangeEndpoints.comparisonB D C f' v d S' I' R' E L h true)
      ha hm' hb
    unfold RationalPurityExchangeEndpoints.comparisonA
      RationalPurityExchangeEndpoints.comparisonB at hp
    unfold RationalPurityExchangeEndpoints.compositeComparison at hp
    exact hp
  · intro E
    constructor
    · have hh := hEnds.unitA E true
      unfold RationalPurityExchangeEndpoints.comparisonA at hh
      unfold RationalPurityExchangeEndpoints.compositeComparison at hh
      exact hh
    · have hh := hEnds.unitB E true
      unfold RationalPurityExchangeEndpoints.comparisonB at hh
      unfold RationalPurityExchangeEndpoints.compositeComparison at hh
      exact hh
  · intro E F L h k
    constructor
    · have hh := hEnds.towerA E F L h k true
      unfold RationalPurityExchangeEndpoints.comparisonA at hh
      unfold RationalPurityExchangeEndpoints.compositeComparison at hh
      exact hh
    · have hh := hEnds.towerB E F L h k true
      unfold RationalPurityExchangeEndpoints.comparisonB at hh
      unfold RationalPurityExchangeEndpoints.compositeComparison at hh
      exact hh
  · intro E
    let := aShift D C u f S E
    let : (H D C f d E ⋙ rationalDerivedPullback C.l E.val u).CommShift ℤ :=
      RationalPurityExchangeEndpoints.shiftA D C u f d S I R E false
    let : (rationalDerivedPullback C.l E.val v ⋙ H D C f' d E).CommShift ℤ :=
      RationalPurityExchangeEndpoints.shiftB D C f' v d S' I' R' E false
    let := bShift D C f' v S' E
    have hs : ShiftCompatibility (A D C u f S E)
        (H D C f d E ⋙ rationalDerivedPullback C.l E.val u)
        (aShift D C u f S E)
        (RationalPurityExchangeEndpoints.shiftA D C u f d S I R E false) (s E) :=
      hEnds.shiftS E
    have hms : ShiftCompatibility
        (H D C f d E ⋙ rationalDerivedPullback C.l E.val u)
        (rationalDerivedPullback C.l E.val v ⋙ H D C f' d E)
        (RationalPurityExchangeEndpoints.shiftA D C u f d S I R E false)
        (RationalPurityExchangeEndpoints.shiftB D C f' v d S' I' R' E false) (mid E) :=
      hShift E
    have ht : ShiftCompatibility
        (rationalDerivedPullback C.l E.val v ⋙ H D C f' d E) (B D C f' v S' E)
        (RationalPurityExchangeEndpoints.shiftB D C f' v d S' I' R' E false)
        (bShift D C f' v S' E) (t E) := hEnds.shiftT E
    exact pasteShift (s E) (mid E) (t E) hs hms ht
  · intro E L h
    constructor
    · have hh := hEnds.shiftComparisonA E L h true
      unfold RationalPurityExchangeEndpoints.comparisonA at hh
      unfold RationalPurityExchangeEndpoints.compositeComparison at hh
      exact hh
    · have hh := hEnds.shiftComparisonB E L h true
      unfold RationalPurityExchangeEndpoints.comparisonB at hh
      unfold RationalPurityExchangeEndpoints.compositeComparison at hh
      exact hh


end Square

section Statement
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
  [IsSeparated f] (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The scalar equation for the specified exchange, as a natural-transformation equality,
with its actual component formula and coefficient unit, tower and shift comparisons.
Geometric consequences are installed from g, rather than assumed of the square.
Source: purity transport, base-change coefficient compatibility
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
def Conclusion (sq : u ≫ f = f' ≫ v) (g : TwistedPullbackScalars.Geometry D C f f' d) : Prop :=
  letI := g.noethX
  letI := g.noethX'
  letI := g.noethY
  letI := g.noethY'
  letI := g.dimX
  letI := g.dimX'
  letI := g.dimY
  letI := g.dimY'
  letI := g.invX
  letI := g.invX'
  letI := g.invY
  letI := g.invY'
  letI := g.finiteF
  letI := g.compactF
  letI := g.separatedF'
  letI := g.finiteF'
  letI := g.compactF'
  letI := g.smoothF'
  ∀ (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
    (S' : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f')),
  ∃ e : ∀ E : AdicPurityScalarNaturality.Field D C, A D C u f S E ≅ B D C f' v S' E,
    (∀ (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E Y),
      (e E).app K = exchange D C u f f' v S S' sq d E K) ∧
    (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
      whiskerRight (e E).hom (T D C E L h X') ≫ (betaB D C f' v S' E L h).hom =
        (betaA D C u f S E L h).hom ≫ whiskerLeft (T D C E L h Y) (e L).hom) ∧
    (∀ E : AdicPurityScalarNaturality.Field D C,
      UnitEquation (betaA D C u f S E E le_rfl) (unit D C E X') (unit D C E Y) ∧
      UnitEquation (betaB D C f' v S' E E le_rfl) (unit D C E X') (unit D C E Y)) ∧
    (∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
      CompositionEquation (betaA D C u f S E F h) (betaA D C u f S F L k)
        (betaA D C u f S E L (h.trans k)) (alpha D C E F L h k X')
        (alpha D C E F L h k Y) ∧
      CompositionEquation (betaB D C f' v S' E F h) (betaB D C f' v S' F L k)
        (betaB D C f' v S' E L (h.trans k)) (alpha D C E F L h k X')
        (alpha D C E F L h k Y)) ∧
    (∀ E : AdicPurityScalarNaturality.Field D C,
      ShiftCompatibility (A D C u f S E) (B D C f' v S' E)
        (aShift D C u f S E) (bShift D C f' v S' E) (e E)) ∧
    (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
      ShiftCompatibility (A D C u f S E ⋙ T D C E L h X')
        (T D C E L h Y ⋙ A D C u f S L)
        (composeShift _ _ (aShift D C u f S E) (tShift D C E L h X'))
        (composeShift _ _ (tShift D C E L h Y) (aShift D C u f S L))
        (betaA D C u f S E L h) ∧
      ShiftCompatibility (B D C f' v S' E ⋙ T D C E L h X')
        (T D C E L h Y ⋙ B D C f' v S' L)
        (composeShift _ _ (bShift D C f' v S' E) (tShift D C E L h X'))
        (composeShift _ _ (tShift D C E L h Y) (bShift D C f' v S' L))
        (betaB D C f' v S' E L h))

/--
The normalization data needed by `assembleExchange` for a fixed pair of exceptional
systems. This is the coefficient-change and base-change coherence step: it supplies
the normalized integral purity families, identifies their rational purity maps with
`gamma`, and identifies the canonical shifted middle comparison with `middle`.
Its source is the smooth-purity transport proof, Steps 1--3.
(blueprint: lem-pur-smooth-exchange-scalar-compatibility)
-/
theorem normalizedExchangeData
    (sq : u ≫ f = f' ≫ v)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f']
    (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
    (S' : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f')) :
    ∃ (I : AdicPurityScalarNaturality.Data D C f d S)
      (I' : AdicPurityScalarNaturality.Data D C f' d S')
      (R : RationalPurityExchangeEndpoints.LocalizedFamily D C f d S I)
      (R' : RationalPurityExchangeEndpoints.LocalizedFamily D C f' d S' I')
      (hEnds : RationalPurityExchangeEndpoints.EndpointEquations
        D C u f f' v d S S' I I' R R')
      (hCanonical : ∀ (E : AdicPurityScalarNaturality.Field D C)
        (K : RCat D C E Y),
        (R.gamma E).app K = gamma D C f S d E K)
      (hCanonical' : ∀ (E : AdicPurityScalarNaturality.Field D C)
        (K : RCat D C E Y'),
        (R'.gamma E).app K = gamma D C f' S' d E K)
      (m : ∀ E : AdicPurityScalarNaturality.Field D C,
        RationalPurityExchangeEndpoints.endpointA D C u f d S E false ≅
          RationalPurityExchangeEndpoints.endpointB D C f' v d S' E false)
      ,
      (∀ (E : AdicPurityScalarNaturality.Field D C)
        (K : RCat D C E Y),
        (m E).app K = middle D C u f f' v sq d E K)
      ∧ (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
        whiskerRight (m E).hom (T D C E L h X') ≫
            (RationalPurityExchangeEndpoints.comparisonB
              D C f' v d S' I' R' E L h false).hom =
          (RationalPurityExchangeEndpoints.comparisonA
            D C u f d S I R E L h false).hom ≫
            whiskerLeft (T D C E L h Y) (m L).hom)
      ∧ (∀ E : AdicPurityScalarNaturality.Field D C,
        ShiftCompatibility
          (RationalPurityExchangeEndpoints.endpointA D C u f d S E false)
          (RationalPurityExchangeEndpoints.endpointB D C f' v d S' E false)
          (RationalPurityExchangeEndpoints.shiftA D C u f d S I R E false)
          (RationalPurityExchangeEndpoints.shiftB D C f' v d S' I' R' E false)
          (m E)) := by
  sorry

set_option linter.style.haveILetI false in
/-- The actual rational smooth exchange commutes with coefficient extension.
Source: current blueprint smooth-purity transport, coefficient-change and base-change
coherence (blueprint: lem-pur-smooth-exchange-scalar-compatibility).
Proof: apply lem-pur-rational-purity-exchange-endpoints. Its domain clause gives
finite-Tor integral representatives of K and Lv*K and the smooth separated finite-type
base change f', without restricting v. Its endpoint squares are
r_A T(s_E) = s_L beta_A and beta_B T(t_E) = t_L r_B, where s is inverse purity
pulled back and t is forward purity. Apply lem-pur-twisted-pullback-square-scalars:
its canonical middle comparison satisfies r_B T(m_E) = m_L r_A. First identify
middle with that m in the shifted-line-first rationalSource coordinates, using
canonical tensor symmetry, shift reassociation, pullback/tensor comparison and
root-line pullback; naturality identifies their common t composite. Reconstruct the
finite inverse-purity / middle / purity composite by
prop-pur-adic-reconstruction-trace-coherence, then rationalize with
prop-weil-pbc-rational-transport. These functors preserve compositions and inverses,
so its result is exactly exchange. Substitute the three squares, in order:
beta_B T(t_E m_E s_E) = t_L r_B T(m_E) T(s_E)
= t_L m_L r_A T(s_E) = t_L m_L s_L beta_A.
Each factor is natural in K, hence this is an equality of natural transformations.
Paste their unit and shift equations. For successive extensions substitute their
coefficient tower equations and cancel the internal tensor associators and inverses;
only the external associators at A and B remain. The degree-zero twist-line
normalization in the middle square precludes any additional sign. -/
-- STATEMENT-DISPUTED: System does not normalize its finiteRight realization or its
-- operation shift structures against the canonical ordinary realization. The planned
-- endpoint theorem requires Data with that extra normalization; its existence for an
-- arbitrary S is not supplied. The pure middle shift law also needs compatible source
-- shifts for the two systems. assembleExchange proves the paste once these are given.
theorem smoothExchangeScalarCompatibility (cartesian : IsPullback u f' f v) :
    ∃ g : TwistedPullbackScalars.Geometry D C f f' d,
      Conclusion D C u f f' v d cartesian.w g := by
  obtain ⟨g, _⟩ := TwistedPullbackScalars.twistedPullbackSquareScalars
    (B := D) (C := C) (u := u) (f := f) (f' := f') (v := v) (d := d) cartesian
  refine ⟨g, ?_⟩
  dsimp only [Conclusion]
  intro S S'
  letI := g.finiteF
  letI := g.compactF
  letI := g.noethX
  letI := g.noethX'
  letI := g.noethY
  letI := g.noethY'
  letI := g.dimX
  letI := g.dimX'
  letI := g.dimY
  letI := g.dimY'
  letI := g.invX
  letI := g.invX'
  letI := g.invY
  letI := g.invY'
  letI := g.finiteF
  letI := g.compactF
  letI := g.separatedF'
  letI := g.finiteF'
  letI := g.compactF'
  letI := g.smoothF'
  obtain ⟨I, I', R, R', hEnds, hCanonical, hCanonical', m, hm, hScalar, hShift⟩ :=
    normalizedExchangeData D C u f f' v (d := d) cartesian.w S S'
  exact assembleExchange D C u f f' v S S' cartesian.w d I I' R R' hEnds
    hCanonical hCanonical' m hm hScalar hShift

end Statement
end WeilConjectures.SmoothExchangeScalarCompatibility
