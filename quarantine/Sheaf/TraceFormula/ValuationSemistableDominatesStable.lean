/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion
import Sheaf.TraceFormula.ValuationComponentFactorization
import Sheaf.TraceFormula.ValuationSeparableClosureExtension

/-! # A semistable modification dominates a stable modification over a valuation ring

Source: Temkin, Stable modification of relative curves, Proposition 4.5.1 and
Corollary 4.4.3(i), with descent from a separable closure for an arbitrary fraction field
(blueprint: lem-trf-valuation-semistable-dominates-stable).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Any semistable generic modification dominates a stable one over a finite-height
valuation ring. Both components of the comparison are over the base and compatible with
the marking. Its generic components are the specified inverse composites.
Source: Temkin, Stable modification of relative curves, Proposition 4.5.1 and
Corollary 4.4.3(i) (blueprint: lem-trf-valuation-semistable-dominates-stable).

Proof plan:
1. For separably closed `K`, use `lem-trf-valuation-common-strict-semistable-refinement`
   to find a common strictly semistable pair `(W,E)` and maps `a,b` with `fa = gb`.
2. By `lem-trf-valuation-contracted-component-inclusion`, every fibre component
   contracted by `b` is also contracted by `a`.
3. A valuation ring is integrally closed (a monic equation for an element outside it
   would put `1` in its maximal ideal). The source of `g` is reduced and generically normal
   by `lem-trf-geometrically-reduced-eta-normal`. Apply
   `lem-trf-valuation-component-factorization` to obtain the curve map. The pulled-back
   marking ideal vanishes generically, hence vanishes by
   `lem-sc-flat-invertible-sections-torsion-free`, applied with the structure sheaf.
   Factor through the closed marking; its monomorphism gives compatibility over `D`.
4. For arbitrary `K`, use `lem-trf-valuation-separable-closure-extension` and pull back
   along its faithfully flat valuation extension. Properness follows from
   `lem-weil-pbc-proper-fp-permanence`; schematic density persists under flat base change.
   Apply `lem-trf-semistable-marked-base-change` and the separably closed case.
5. Over the tensor square of the extension the two maps agree generically. Their
   equalizer is closed since the stable map is proper and thus separated. Flatness over
   the original domain and `lem-sc-flat-invertible-sections-torsion-free` kill its ideal.
   The same argument applies to the marking; the overlap need not be a valuation ring.
6. Apply `lem-weil-pbc-fpqc-representable-descent` separately to both maps. Descent also
   reflects the marking square and the equations `fh = g`. On the generic fibre these
   equations give the inverse composites because the two components of `f` are invertible.
-/
theorem exists_semistable_to_stable_valuation_comparison
    (K : Type u) [Field K] (V : ValuationSubring K) [Finite (PrimeSpectrum V)]
    (P Pst P' : MultipointedCurve (Spec (.of V)))
    (hXη : Smooth (pullback.snd P.x (Spec.map (CommRingCat.ofHom V.subtype))))
    (hDη : Etale (pullback.snd P.d (Spec.map (CommRingCat.ofHom V.subtype))))
    (f : MultipointedCurve.Hom Pst P) (g : MultipointedCurve.Hom P' P)
    (hf : f.IsStable (Spec.map (CommRingCat.ofHom V.subtype)))
    (hg : g.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)))
    (hsemistable : P'.IsSemistable) :
    ∃ h : MultipointedCurve.Hom P' Pst,
      h.curve ≫ f.curve = g.curve ∧ h.marking ≫ f.marking = g.marking ∧
      h.curveBaseChange (Spec.map (CommRingCat.ofHom V.subtype)) =
        g.curveBaseChange (Spec.map (CommRingCat.ofHom V.subtype)) ≫
          @inv Scheme.{u} _ _ _
            (f.curveBaseChange (Spec.map (CommRingCat.ofHom V.subtype))) hf.1.2.2.2.2.1 ∧
      h.markingBaseChange (Spec.map (CommRingCat.ofHom V.subtype)) =
        g.markingBaseChange (Spec.map (CommRingCat.ofHom V.subtype)) ≫
          @inv Scheme.{u} _ _ _
            (f.markingBaseChange (Spec.map (CommRingCat.ofHom V.subtype)))
              hf.1.2.2.2.2.2 := by
  sorry

end AlgebraicGeometry
