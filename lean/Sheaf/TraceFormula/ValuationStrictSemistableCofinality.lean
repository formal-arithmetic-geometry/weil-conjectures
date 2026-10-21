/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Sheaf.TraceFormula.Modification
public import Sheaf.TraceFormula.StrictSemistableCurve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal
import Sheaf.TraceFormula.FiniteFibreValuationDomination
import Sheaf.TraceFormula.SingleValuationSemistableExtraction
import Sheaf.TraceFormula.ValuationHorizontalCurveModels

/-! # Strictly semistable modifications are cofinal over a strict model

Source: Temkin, *Stable modification of relative curves*, Proposition 4.3.1,
pp. 27--29 (blueprint: lem-trf-valuation-strict-semistable-cofinality).

The proof is postponed. It follows the finite valuation reduction, the iterative
single-valuation extraction, and the final domination argument of Proposition 4.3.1.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Strictly semistable modifications are cofinal over a strict model.
Source: Temkin, *Stable modification of relative curves*, Proposition 4.3.1,
pp. 27--29 (blueprint: lem-trf-valuation-strict-semistable-cofinality).

Proof plan, following the node's six steps:
1. By `lem-trf-strict-semistable-model-normal`, `Ydata.Y` is normal and reduced.
   The empty-marking case of `lem-trf-valuation-horizontal-curve-models` gives finitely
   many components. The dense isomorphism opens and the injection of structure sheaves
   imply that `W` is reduced: a nilpotent section restricts to zero on the reduced open.
   Applying the horizontal-model result to `q` now shows that `W` is a relative curve
   and that `q` induces an isomorphism on the generic fibre.
2. Apply `lem-trf-finite-fibre-valuation-domination` to `q`. It produces a finite family
   of centred component-field valuations with residual transcendence degree one and
   closed centres on `Ydata.Y`. A normal modification of this fixed target dominates
   `W` as soon as every member has a fibre-generic centre on it.
3. The generic point is open in the base: for a field this is immediate; otherwise
   invert a nonzero element in the least nonzero prime of the finite chain. On each
   flat affine chart the ring injects into its generic localization. Thus the generic
   fibre is schematically dense. Proper maps between these curves which are generic
   isomorphisms are eta-modifications. Their composites have the same property, using
   `lem-weil-pbc-proper-fp-permanence` for composition of proper morphisms.
4. Start with the identity modification of the strict model. After extracting the first
   `j` valuations, normality of the current model and smoothness of its generic fibre
   still hold. The domination lemma lifts the next centred valuation uniquely. If its
   centre is already fibre-generic do nothing; otherwise its centre is closed, and
   `lem-trf-single-valuation-semistable-extraction` supplies a strict eta-modification
   making that centre fibre-generic. Compose it with the map to the original model.
5. The persistence clause of the domination lemma says that a modification of a normal
   curve is an isomorphism near each preceding fibre-generic centre. Thus the induction
   retains the centres already extracted. After finitely many steps all are extracted;
   an empty family requires no extraction and leaves the original model.
6. The final strict model is normal. The domination criterion supplies `z` to `W` and
   `p` to the original curve with `z ≫ q = p`. Both `p` and `q` are generic isomorphisms,
   hence so is `z`, whose generic map is the composite of the first with the inverse
   of the second. The map `z` is proper: its graph over the original curve is closed
   because `q` is separated, and its projection is a base change of the proper map `p`.
   Generic density and generic isomorphy give the required dense isomorphism opens.
   Consequently both displayed maps are eta-modifications.
-/
theorem exists_strictSemistable_etaModification
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)] (Ydata : StrictSemistableCurve (Spec (.of V)))
    (hgeneric : Smooth (pullback.snd Ydata.structureMap
      (Spec.map (CommRingCat.ofHom V.subtype))))
    (W : Scheme.{u}) (q : W ⟶ Ydata.Y) (hq : SchemeModification q) :
    ∃ (Zdata : StrictSemistableCurve (Spec (.of V)))
      (z : Zdata.Y ⟶ W) (p : Zdata.Y ⟶ Ydata.Y),
      z ≫ q = p ∧ p ≫ Ydata.structureMap = Zdata.structureMap ∧
      EtaModification (Spec.map (CommRingCat.ofHom V.subtype))
        z (q ≫ Ydata.structureMap) ∧
      EtaModification (Spec.map (CommRingCat.ofHom V.subtype))
        p Ydata.structureMap := by
  sorry

end AlgebraicGeometry
