/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalSmoothPurityCanonical
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackSquareScalars
public import WeilConjectures.AlgebraicGeometry.RationalPurityExchangeEndpoints
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso

/-! # Canonical maps of the smooth purity exchange

Source: current blueprint sec-smooth-purity/sk-thm-purity-transport,
coefficient-change and base-change coherence
(blueprint: def-pur-smooth-exchange-canonical-maps).

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

private theorem inverse_scalar_square
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {X Y : A} {X' Y' : B} (e : X ≅ Y) (e' : X' ≅ Y')
    (a : F.obj X ⟶ X') (b : F.obj Y ⟶ Y')
    (h : F.map e.hom ≫ b = a ≫ e'.hom) : F.map e.inv ≫ a = b ≫ e'.inv := by
  apply (Iso.cancel_iso_hom_left (F.mapIso e) _ _).mp
  change F.map e.hom ≫ (F.map e.inv ≫ a) = F.map e.hom ≫ (b ≫ e'.inv)
  rw [← Category.assoc, ← F.map_comp, e.hom_inv_id, F.map_id, Category.id_comp,
    ← Category.assoc, h, Category.assoc, e'.hom_inv_id, Category.comp_id]


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

attribute [local implicit_reducible] H T G O
  ConstructibleExceptionalCoefficients.category
  AdicPurityScalarNaturality.fieldStage ConstructibleExceptionalCoefficients.FieldComparison.b
attribute [local semireducible] b
attribute [local irreducible] gamma RationalSmoothPurityCanonical.rationalIso
  ScalarLocalization.composition sfIntegralConstructible sfIntegralConstructibleLinear
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory AlgebraicGeometry.Scheme.residueField
  ScalarLocalization.category

/-- The constructed rational purity map satisfies the specified scalar square.
Source: rational purity, coefficient change
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
theorem gamma_scalar (d : ℕ) [SmoothOfRelativeDimension d f]
    (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) (K : RCat D C E Y) :
    (T D C E L h X).map (gamma D C f S d E K).hom ≫
        (b D C f S E L h).hom.app K =
      (RationalSmoothPurityCanonical.sourceScalar C.l E.val L.val
        (IntermediateField.inclusion h) f d K).hom ≫
        (gamma D C f S d L ((T D C E L h Y).obj K)).hom := by
  unfold gamma b
  exact RationalSmoothPurityCanonical.rationalIso_scalar (setting D C E) f
    (integralExceptionalCompactification D f) S L (IntermediateField.inclusion h) d K

/-- Cancellation gives the inverse-purity scalar square.
Source: rational purity, coefficient change
(blueprint: lem-pur-smooth-exchange-scalar-compatibility). -/
theorem gamma_scalar_inv (d : ℕ) [SmoothOfRelativeDimension d f]
    (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) (K : RCat D C E Y) :
    (T D C E L h X).map (gamma D C f S d E K).inv ≫
        (RationalSmoothPurityCanonical.sourceScalar C.l E.val L.val
          (IntermediateField.inclusion h) f d K).hom =
      (b D C f S E L h).hom.app K ≫
        (gamma D C f S d L ((T D C E L h Y).obj K)).inv := by
  exact inverse_scalar_square (T D C E L h X)
    (gamma D C f S d E K) (gamma D C f S d L ((T D C E L h Y).obj K))
    (RationalSmoothPurityCanonical.sourceScalar C.l E.val L.val
      (IntermediateField.inclusion h) f d K).hom ((b D C f S E L h).hom.app K)
    (gamma_scalar D C f S d E L h K)

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

end Square
end WeilConjectures.SmoothExchangeScalarCompatibility
