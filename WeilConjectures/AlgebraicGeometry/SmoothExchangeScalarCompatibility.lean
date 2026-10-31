/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalSmoothPurityCanonical
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackSquareScalars
public import WeilConjectures.AlgebraicGeometry.RationalPurityExchangeEndpoints
public import WeilConjectures.AlgebraicGeometry.SmoothExchangeCanonicalMaps

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

attribute [local implicit_reducible] A B T
attribute [local irreducible] gamma RationalSmoothPurityCanonical.rationalIso
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
-- STATEMENT-DISPUTED: System permits arbitrary replacement of finiteRight, whereas
-- Data requires FiniteRightNormalized. See the E4 change record.
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
  simpa only [] using assembleExchange D C u f f' v S S' cartesian.w d I I' R R' hEnds
    hCanonical hCanonical' m hm hScalar hShift

end Statement
end WeilConjectures.SmoothExchangeScalarCompatibility
