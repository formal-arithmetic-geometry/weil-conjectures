/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.AlgebraicGeometry.StrictlySemistableCurve
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Sheaf.AlgebraicGeometry.BirationalQuasiModificationCommonCover
import Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion
import Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction
import Sheaf.Compactification.BoundaryRefinement
import Sheaf.TraceFormula.ValuationComponentFactorization
import Sheaf.TraceFormula.ValuationHorizontalCurveModels
import Sheaf.TraceFormula.ValuationMarkingSemistableSeparation
import Sheaf.TraceFormula.ValuationStrictSemistableCofinality
import Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization
import WeilConjectures.Compactification.Dense

/-! # Common strict semistable refinements of curve models

Source: Temkin, *Stable modification of relative curves*, Proposition 4.5.1 and
Remark 4.5.2 (blueprint: lem-trf-valuation-common-strict-semistable-refinement).

The proof is postponed. It constructs a reduced common modification, glues the
local stable refinements, and applies strict semistable cofinality to the resulting
marked semistable pair. The chart predicate `IsStrictlySemistableCurve` records the
strict curve charts; `MultipointedCurve.IsSemistable` records the etale marking and
ordinary-double-point fibre condition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.MultipointedCurve

/-- Two eta-modifications of a smooth-generic marked curve admit a common strictly
semistable marked refinement.

Source: Temkin, *Stable modification of relative curves*, Proposition 4.5.1 and
Remark 4.5.2 (blueprint: lem-trf-valuation-common-strict-semistable-refinement).

Proof plan:
1. Form the reduced closure of the common generic curve in the product of the two
   given modifications. The horizontal-curve construction supplies its flat
   multipointed-curve structure and the closure of the generic marking.
2. Cover this reduced modification by strict local models and apply stable
   semistable refinement on each member. On overlaps, the component comparison
   criterion gives unique pair isomorphisms, including the markings; separatedness
   and flat generic-density make the comparisons satisfy the cocycle condition.
3. Glue the local pairs and their maps. Properness and the eta-isomorphism are
   checked on the target cover, and the glued pair is semistable.
4. Apply strict semistable refinement to the single global semistable pair and
   compose with the maps to the two original models. The two composites agree
   because the reduced common product was formed over the original curve.

Empty markings and empty curves are allowed by `MultipointedCurve`; no
semistability, stability, separatedness, or properness hypothesis is imposed on
`X₁` or `X₂` beyond the displayed eta-modification hypotheses. -/
theorem exists_common_strictSemistable_refinement
    (K : Type u) [Field K] [IsSepClosed K]
    (V : ValuationSubring K) [Finite (PrimeSpectrum V)]
    (C : MultipointedCurve (Spec (.of V)))
    (hsmooth : Smooth (pullback.snd C.x
      (Spec.map (CommRingCat.ofHom V.subtype))))
    (hetale : Etale (pullback.snd C.d
      (Spec.map (CommRingCat.ofHom V.subtype))))
    (X₁ X₂ : MultipointedCurve (Spec (.of V)))
    (f₁ : X₁.Hom C) (f₂ : X₂.Hom C)
    (hf₁ : f₁.IsEtaModification
      (Spec.map (CommRingCat.ofHom V.subtype)))
    (hf₂ : f₂.IsEtaModification
      (Spec.map (CommRingCat.ofHom V.subtype))) :
    ∃ (W : MultipointedCurve (Spec (.of V)))
      (q₁ : W.Hom X₁) (q₂ : W.Hom X₂),
      (IsStrictlySemistableCurve W.x ∧ W.IsSemistable) ∧
        q₁.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)) ∧
        q₂.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)) ∧
        q₁.curve ≫ f₁.curve = q₂.curve ≫ f₂.curve ∧
        q₁.marking ≫ f₁.marking = q₂.marking ≫ f₂.marking := by
  sorry

end AlgebraicGeometry.MultipointedCurve
