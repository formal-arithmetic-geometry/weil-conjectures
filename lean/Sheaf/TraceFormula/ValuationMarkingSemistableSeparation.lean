/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.AlgebraicGeometry.StrictlySemistableCurve
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction
import Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension
import Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree
import Sheaf.TraceFormula.ValuationHorizontalCurveModels
import Sheaf.TraceFormula.ValuationStrictSemistableCofinality
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.Blowup.AdmissibleBlowup
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.Affine.Defs
import WeilConjectures.Blowup.BlowupUniversal
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Gluing
import WeilConjectures.Blowup.Proper
import WeilConjectures.Compactification.FiniteTypeExtension
import WeilConjectures.Compactification.StrictTransform
import Sheaf.AlgebraicGeometry.StrictTransformFlatBaseChange

/-! # Semistable separation of a marking over a valuation ring

Source: Temkin, *Stable modification of relative curves*, Lemma 4.3.2, p. 29;
semistability conclusion for the marked pair
(blueprint: lem-trf-valuation-marking-semistable-separation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A generic étale marking on a strictly semistable curve over a finite-height
separably closed valuation ring admits a semistable eta-modification.

Source: Temkin, *Stable modification of relative curves*, Lemma 4.3.2, p. 29
(blueprint: lem-trf-valuation-marking-semistable-separation).
The hypotheses are: a field `K` with a separable-closed instance, a valuation
subring `V` with finite prime spectrum, a multipointed curve `C` over `Spec V`,
strict semistability of its curve morphism, and smooth generic curve with étale
generic marking. The conclusion is a multipointed curve `C'`, a morphism
`f : C'.Hom C`, its eta-modification property, and semistability of `C'`.
-/
theorem exists_semistableEtaModification_of_isSepClosed
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)] (C : MultipointedCurve (Spec (.of V)))
    (hstrict : IsStrictlySemistableCurve C.x)
    (hsmooth : Smooth (pullback.snd C.x
      (Spec.map (CommRingCat.ofHom V.subtype))))
    (hmarking : Etale (pullback.snd C.d
      (Spec.map (CommRingCat.ofHom V.subtype)))) :
    ∃ (C' : MultipointedCurve (Spec (.of V))) (f : C'.Hom C),
      f.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)) ∧
        C'.IsSemistable := by
  sorry

end AlgebraicGeometry
