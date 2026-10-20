/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown
import Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion

/-! # Contracting a given semistable modification to a stable modification

Source: Temkin, Stable modification of relative curves, Proposition 4.4.6, pp. 32--33
(blueprint: lem-trf-valuation-semistable-stable-contraction).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Temkin

/-- Every given semistable eta-modification factors, by an eta-modification, through a stable
one over a finite-height valuation ring with separably closed fraction field.
Source: Temkin, Proposition 4.4.6 (blueprint: lem-trf-valuation-semistable-stable-contraction).

Proof plan:
1. The generic fibres of all flat schemes here, including the markings, are schematically
   dense opens. In height zero they are the whole scheme. Otherwise a nonzero element in the
   smallest nonzero prime cuts out their complement, and flatness makes localization injective
   (def-weil-flat-morphism and def-weil-pbc-flat-ring-map).
2. By lem-trf-valuation-exceptional-closed-image-criterion the set of fibre-component generic
   points with closed image in the fixed target is finite. Induct strongly on its cardinality.
   If the given map is stable, take the identity factorization; cardinality zero is this case.
3. Otherwise that criterion supplies an exceptional component. Apply
   lem-trf-valuation-exceptional-blowdown. Its semistable blowdown removes exactly one point
   from the finite set. Apply induction to the resulting map to the same target and compose.
4. Properness on curves and markings is preserved under composition by
   lem-weil-pbc-proper-fp-permanence(a); generic fibre maps compose as isomorphisms. Step 1
   supplies the schematically dense opens, so the composite factor is an eta-modification. -/
theorem valuation_semistable_stable_contraction
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)]
    (X Y : MultipointedCurve (Spec (.of V)))
    (hX : Smooth (pullback.snd X.x (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (hD : Etale (pullback.snd X.d
      (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (f : Y.Hom X)
    (hf : f.IsEtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)))
    (hY : Y.IsSemistable) :
    ∃ (Z : MultipointedCurve (Spec (.of V))) (g : Z.Hom X) (q : Y.Hom Z),
      g.IsStable (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) ∧
      q.IsEtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) ∧
      q.curve ≫ g.curve = f.curve ∧ q.marking ≫ g.marking = f.marking := by
  sorry

end AlgebraicGeometry.Temkin
