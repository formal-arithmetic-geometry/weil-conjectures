/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurReductionLimitShiftData
public import Sheaf.Paper.SequenceKInjectiveComparisonShifts

/-! # Signed Roos triangles for the canonical coefficient limit

Source: Stacks 06YY, 07A6 and 0941; current blueprint
`sk-thm-sf-compatibility/fix-prop-coherence.proof.md`, coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The canonical coefficient limit admits Roos triangles on every supplied
K-injective replacement, with the canonical replacement-model shift equation,
their actual projections and signed shift equations.
Source: Stacks 0941, proof of lemma-derived-limit-is-ok, and cochain cone convention
014E, refined by the explicit signed cone calculation
(blueprint: lem-pur-coefficient-roos-shift-normalization).

Proof: first use a K-injective replacement with injective tower terms. Evaluation
preserves K-injectivity, and the termwise product is a product after localization.
The prefix-tower lifting argument splits every transition in each degree. Thus
1-s is termwise split epic, its kernel is the actual limit, and the kernel
inclusion (0,x) into Cone(1-s)[-1] is a quasi-isomorphism. Inverse rotation and
localization give the distinguished triangle. Its first arrow consists of the
actual limit projections; transport its first vertex along purCoefficientLimitModel.
On the shifted cone the map (y,x) maps to ((-1)^r y,x). It commutes with the
kernel inclusion and with the projection to x. Insertion in y gains (-1)^r,
so the connecting map has exactly the displayed sign and shift commutator.
For an arbitrary K-injective tower I, compare it to a replacement with injective
terms. The comparison is a homotopy equivalence. Limit, evaluation, product and
the Roos cone preserve tower homotopies, so transport these identities back to I.
The same computation on comparison maps proves naturality and independence.
Choose the boundary by this natural transport; its shift square holds for every
shifted replacement, not only selected representatives. The proved canonical
replacement-shift equation identifies the transported limit shift with the fixed
one used here. Products need not be exact. Zero shift is identity; r=1 and -1
negate the first coordinate, and signs multiply for repeated shifts. Zero towers
and the empty scheme give the zero triangle. -/
theorem purCoefficientRoosShiftNormalization
    [products : HasCountableProducts (DerivedCategory (scalarReductionSource l E W))] :
    letI := SequenceKInjectiveComparison.totalLimitCommShift l E W
    (∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
    (r : ℤ) [(I⟦r⟧).IsKInjective]
    [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
    (coefficientSequenceLimit l E W).map
        ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
        (DerivedCategory.Q.obj N) ≫
      (purCoefficientLimitModel l E W N I j).hom⟦r⟧' =
    (purCoefficientLimitModel l E W (N⟦r⟧) (I⟦r⟧)
      (purCoefficientShiftedResolution l E W N I j r)).hom ≫
      DerivedCategory.Q.map
        ((((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app I) ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∃ roos : (∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j],
      PurCoefficientRoosTriangle l E W N I j),
      (∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
      (r : ℤ) [(I⟦r⟧).IsKInjective]
      [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).p ≫
        (purCoefficientRoosProductShift l E W I r).hom =
      (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
        ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
          (DerivedCategory.Q.obj N) ≫ (roos N I j).p⟦r⟧') ∧
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).δ ≫
        ((coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
          ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
            (DerivedCategory.Q.obj N))⟦(1 : ℤ)⟧' =
      r.negOnePow • ((purCoefficientRoosProductShift l E W I r).hom ≫
        (roos N I j).δ⟦r⟧' ≫ (shiftFunctorComm _ 1 r).hom.app
          ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N)))))) := by sorry

end WeilConjectures
