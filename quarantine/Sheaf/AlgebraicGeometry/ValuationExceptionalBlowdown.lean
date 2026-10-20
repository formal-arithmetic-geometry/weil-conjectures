/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Sober

import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.TraceFormula.ValuationHorizontalCurveModels
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.TraceFormula.FiniteFibreValuationDomination
import Sheaf.TraceFormula.ValuationCurveProjectivePreparation
import Sheaf.TraceFormula.ValuationExceptionalLocalCriterion
import Sheaf.TraceFormula.ValuationNodalPolarSection
import Sheaf.TraceFormula.ValuationNormalizedGraphModel

/-! # One exceptional blow-down over a finite-height valuation ring

Source: Temkin, *Stable modification of relative curves*, definition of exceptional
blow-down and Lemma 4.4.5, p. 32; proof of Proposition 4.4.6, pp. 32--33
(blueprint: lem-trf-valuation-exceptional-blowdown).

The set `B_f` and exceptionality are the landed
`MultipointedCurve.Hom.closedImageFiberGenericPoints` and
`MultipointedCurve.Hom.IsExceptionalFiberGenericPoint`
(lem-trf-valuation-exceptional-closed-image-criterion), whose node defines them by the
same text as this node.

## Main statements

* `Temkin.valuation_exceptional_blowdown`: contract a specified exceptional component
  and remove exactly its generic point from this set.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace Temkin

/-- A specified exceptional component with closed image admits a semistable blow-down.
Exceptionality of the generic point of `C` is `IsExceptionalFiberGenericPoint`: `f` contracts
the reduced component, its base change to the algebraic closure of the residue field is a
projective line, and it meets the geometric special points in at most two points.
Source: Temkin, Lemma 4.4.5 and the proof of Proposition 4.4.6, pp. 32--33
(blueprint: lem-trf-valuation-exceptional-blowdown).

Proof plan:
1. By lem-trf-geometrically-reduced-eta-normal the semistable source is reduced and
   eta-normal. Use lem-trf-valuation-curve-projective-preparation to normalize source
   and target, factor through the target normalization, localize the valuation base
   beneath the closed image, and prepare a normal projective compactification.
   Finite normalization preserves the original closed-image set in both directions.
2. By lem-trf-valuation-nodal-polar-section the exceptional component descends to a
   projective line over the residue field. Choose polar divisors on all other
   closed-fibre components and the two sections e = 1 and a of their line bundle.
   Their common zero set has empty closed fibre, hence is empty by properness over
   the local base.
3. The reciprocal affine coordinates a/e and e/a define the projective-line map.
   It is constant on C, since global functions on a projective line are constant,
   and nonconstant on every other component because of the specified poles.
4. Normalize the relative graph using lem-trf-valuation-normalized-graph-model.
   Only C is contracted in the prepared closed fibre. The locality clause of
   lem-trf-valuation-curve-projective-preparation spreads and glues back to the
   original target. Exactly C among components with closed image is contracted;
   nothing is asserted about components whose image in that target is not closed.
5. By lem-trf-valuation-horizontal-curve-models the generic marking's schematic
   closure defines the intermediate multipointed curve. Uniqueness of the flat
   closure identifies the source marking. Both arrows are eta-modifications of
   pairs, and both curve and marking maps factor the original maps.
6. At a closed point of the intermediate curve where h is not an isomorphism,
   lem-trf-valuation-normalized-graph-model gives a connected positive-dimensional
   fibre. Its support has finitely many irreducible components, using
   lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-noetherian-finitely-many-components. Properness makes its image in
   the original target closed. Step 4 forces its one-dimensional components to
   equal C; an extra isolated point would disconnect the fibre. Thus its reduced
   subcurve is C. This makes no assertion about embedded associated points.
7. Apply lem-trf-valuation-exceptional-local-criterion to this exceptional
   projective-line fibre, with at most two boundary and marking points. It gives
   semistability at its image. Elsewhere h is locally an isomorphism of marked
   pairs. Openness of semistability and the closed-point test on the quasi-compact
   intermediate curve give semistability everywhere.
8. By lem-trf-finite-fibre-valuation-domination h is an isomorphism near each
   target fibre generic point. Noncontracted source components correspond exactly
   to target components. The factorization preserves closedness of images in the
   unchanged target; Step 4 removes exactly the generic point of C. This is the
   displayed bijection, and the previous steps give the remaining clauses. -/
theorem valuation_exceptional_blowdown
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)]
    (X Y : MultipointedCurve (Spec (.of V)))
    (hX : Smooth (pullback.snd X.x (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (hD : Etale (pullback.snd X.d (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (f : Y.Hom X)
    (hf : f.IsEtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)))
    (hY : Y.IsSemistable)
    (t : Spec (.of V)) (C : Set (Y.x.fiber t))
    (hC : C ∈ irreducibleComponents (Y.x.fiber t))
    (z : Y.x.fiber t) (hz : IsGenericPoint z C)
    (hclosed : IsClosed ({f.curve (Y.x.fiberι t z)} : Set X.X))
    (hexceptional : f.IsExceptionalFiberGenericPoint (Y.x.fiberι t z)) :
    ∃ (Y₁ : MultipointedCurve (Spec (.of V))) (f₁ : Y₁.Hom X) (h : Y.Hom Y₁),
      f₁.IsEtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) ∧
      Y₁.IsSemistable ∧
      h.IsEtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) ∧
      h.curve ≫ f₁.curve = f.curve ∧ h.marking ≫ f₁.marking = f.marking ∧
      (h.curve '' (Y.x.fiberι t '' C)).Subsingleton ∧
      Set.BijOn h.curve
        (f.closedImageFiberGenericPoints \ {Y.x.fiberι t z})
        f₁.closedImageFiberGenericPoints := by
  sorry

end Temkin

end AlgebraicGeometry
