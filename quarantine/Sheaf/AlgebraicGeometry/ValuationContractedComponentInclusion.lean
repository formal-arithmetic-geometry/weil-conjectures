/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring

import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.TraceFormula.SemistableModificationFibreContractions
import Sheaf.AlgebraicGeometry.SepClosedValuationGeometricComponents
import Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness

/-! # Inclusion of contracted fibre components in a common semistable model

Source: Temkin, *Stable modification of relative curves*, proof of Corollary 4.4.3(i),
printed p. 31, with the standing hypotheses of Section 4
(blueprint: lem-trf-valuation-contracted-component-inclusion).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A component of a common semistable model contracted in a semistable target is also
contracted in the stable target. This is only a statement about topological images in
scheme-theoretic fibres; it does not assert a factorization of the family morphisms.
Source: Temkin, proof of Corollary 4.4.3(i), printed p. 31
(blueprint: lem-trf-valuation-contracted-component-inclusion).

Proof plan:
1. Fix a base point `s` and a component `Z` contracted by `b`. By
   `lem-trf-sepclosed-valuation-geometric-components`, its residue field is separably closed.
   Its algebraic closure is purely inseparable by `lem-pc-kbar-pure-insep`, and
   `lem-pc-homeo-pure-insep` makes the projections from the geometric fibres of `W`, `X`,
   and `Y` homeomorphisms. The corresponding geometric component is still contracted by `b`.
2. The generic isomorphisms transfer smoothness and etaleness from `C` to `X`, `Y`, and `W`.
   Apply `lem-trf-semistable-modification-fibre-contractions` to the given family
   eta-modifications `a` and `b`. Their geometric fibre maps are finite sequences of
   elementary exceptional contractions, with semistable intermediate pointed curves.
   `lem-trf-semistable-marked-base-change` gives geometric stability of `f`.
3. Set `r = fa = gb` on the geometric fibre. Every stage contracted in either sequence is
   `r`-exceptional, since its remaining map to `X` or `Y`, and hence to `C`, is constant.
   The terminal `a` quotient is stable relative to `r`. Apply
   `lem-trf-valuation-stable-blowdown-uniqueness` to these contraction sequences to get
   the geometric-fibre factorization `a = u b`. Thus `a` contracts the component too.
4. The base-change square commutes, and the projection of the lifted component is `Z`.
   Its singleton `a`-image projects to precisely the `a`-image of `Z`. This descends the
   assertion to the original scheme-theoretic fibre, for every `s` and every component.
-/
theorem valuation_contracted_component_inclusion
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)]
    (C X Y W : MultipointedCurve (Spec (.of V)))
    (hCη : Smooth (pullback.snd C.x (Spec.map (CommRingCat.ofHom V.subtype))))
    (hDη : Etale (pullback.snd C.d (Spec.map (CommRingCat.ofHom V.subtype))))
    (f : X.Hom C) (g : Y.Hom C) (a : W.Hom X) (b : W.Hom Y)
    (hf : f.IsStable (Spec.map (CommRingCat.ofHom V.subtype)))
    (hg : g.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)))
    (hY : Y.IsSemistable) (hW : W.IsSemistable)
    (ha : a.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)))
    (hb : b.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)))
    (hcomm : a.curve ≫ f.curve = b.curve ≫ g.curve ∧
      a.marking ≫ f.marking = b.marking ≫ g.marking) :
    ∀ (s : Spec (.of V)) (Z : Set (W.x.fiber s)),
      Z ∈ irreducibleComponents (W.x.fiber s) →
      Set.Subsingleton
        ((b.curveBaseChange ((Spec (.of V)).fromSpecResidueField s)) '' Z) →
      Set.Subsingleton
        ((a.curveBaseChange ((Spec (.of V)).fromSpecResidueField s)) '' Z) := by
  sorry

end AlgebraicGeometry
