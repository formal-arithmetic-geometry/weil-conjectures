/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.TraceFormula.StrictSemistableCurve
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.FiniteEtaleClosedSubschemeSection
import Mathlib.RingTheory.Smooth.Basic
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover
import Sheaf.RingTheory.VerticalPrincipalIdealFibreDetection
import Sheaf.AlgebraicGeometry.OrderedNodalBranchOverlap
/-! # Zariski strict pair charts from smooth fibre branches

Source: Temkin, Stable Modification of Relative Curves, §4.3, p. 27 and Remark 4.5.2,
p. 33, for the chart notion; the relative all-fibres criterion and seven-step descent
argument are the DAG's reconstruction from Stacks 0CBY
(blueprint: lem-trf-valuation-smooth-branches-strict-chart).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A semistable multipointed curve over a finite-height separably closed valuation
base has Zariski strict pair charts if every reduced component of every fibre is smooth.
The smooth case includes an étale map of markings to the zero section. At a marked
point its square is cartesian; at an unmarked point the source marking is empty.
The nonsmooth case has a nodal chart and empty source marking.

Source: Temkin §4.3, p. 27 and Remark 4.5.2, p. 33 (chart notion); agent-reconstructed
relative criterion from Stacks 0CBY
(blueprint: lem-trf-valuation-smooth-branches-strict-chart).

Proof plan, following the seven steps of the node:
1. On the relative smooth locus use lem-pur-smooth-pair-local-coordinates at a marked
   point, with relative dimensions zero and one. At an unmarked point remove the closed
   marking and use sbc-thm-etale-local-normal-form. Restrict to affine neighbourhoods.
2. At a nonsmooth point remove the marking and apply lem-trf-nodal-family-etale-local-model.
   A valuation ring is normal: a monic integral equation for an element outside it,
   divided by its highest power, would put one in its maximal ideal. Apply
   lem-weil-pbc-gabber-finite-etale-section to remove the étale base neighbourhood.
   Smoothness is reflected by the étale source cover using
   lem-sbc-smooth-flat-surjective-source-descent, so the chosen chart point is a node.
   Use lem-weil-pbc-flat-lfp-open for the open images and
   lem-trf-space-chartwise-etale-permanence and
   lem-weil-pbc-smooth-ring-map-base-change-composition for permanence.
3. The thickness c is nonzero: otherwise openness of the chart image would produce a
   nonsmooth generic point, contrary to the smooth generic curve. Flatness then makes
   both nodal coordinates nonzerodivisors, invertible generically. Apply
   lem-trf-ordered-nodal-branch-overlap to order their fibre-generic ideals on overlaps.
4. The overlap is flat and finitely presented, with geometrically reduced fibres by
   etale-proposition-etale-reduced, since each standard nodal fibre is reduced. Apply
   lem-trf-vertical-principal-ideal-fibre-detection to each coordinate. Their pullback
   ideals agree on the whole overlap; as actual submodules the identifications obey
   the cocycle condition. Étale smoothness uses
   lem-weil-pbc-etale-smooth-zero-dimensional-fibres.
5. Apply lem-pc-fpqc-descent to the two invertible ideals and their inclusions. Descend
   their product equality IJ = (c). Choose Zariski-local generators u,v; rescale one
   by a unit so that uv = c. This defines the desired nodal morphism. Its pullback
   coordinates are alpha*u0 and alpha^(-1)*v0, since c is a nonzerodivisor.
6. On Y times Gm the map (u,v) = (t*u0,t^(-1)*v0) is étale over the nodal model
   times Gm. The graph t = alpha gives the new morphism. At points over x both
   coordinates vanish, so differentiation over the nodal model gives d(alpha)/dt = 0.
   The graph equation has derivative one. The square-Jacobian criterion
   lem-exc-etale-jacobian-presentation gives étaleness near every point above x.
7. Restrict to that open, whose image contains x, and apply
   lem-trf-etale-descent-through-source-cover. Choose an affine neighbourhood of x.
   Its marking is empty. Together with step 1 this supplies all the asserted cases.
-/
theorem exists_valuation_smooth_branches_strict_chart
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)] (P : MultipointedCurve (Spec (.of V)))
    (hsemistable : P.IsSemistable)
    (hgeneric : Smooth (pullback.snd P.x (Spec.map (CommRingCat.ofHom V.subtype))))
    (hcomponents : ∀ (s : Spec (.of V)) (Z : TopologicalSpace.Closeds (P.x.fiber s)),
      (Z : Set (P.x.fiber s)) ∈ irreducibleComponents (P.x.fiber s) →
        Smooth ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
          P.x.fiberToSpecResidueField s)) :
    ∀ x : P.X, ∃ (U : P.X.Opens) (B : (Spec (.of V)).Opens)
      (_ : IsAffineOpen U) (hB : IsAffineOpen B),
      x ∈ U ∧ P.x x ∈ B ∧ U ≤ P.x ⁻¹ᵁ B ∧
      ((x ∈ P.x.smoothLocus ∧
        ∃ (h : U.toScheme ⟶ Spec (.of (Polynomial Γ(Spec (.of V), B))))
          (m : pullback (C := Scheme) P.i U.ι ⟶ Spec Γ(Spec (.of V), B)),
          Etale h ∧ Etale m ∧
          h ≫ Spec.map (CommRingCat.ofHom Polynomial.C) ≫ hB.fromSpec = U.ι ≫ P.x ∧
          m ≫ hB.fromSpec = pullback.fst P.i U.ι ≫ P.d ∧
          m ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)) =
            pullback.snd P.i U.ι ≫ h ∧
          (x ∈ Set.range P.i →
            IsPullback m (pullback.snd P.i U.ι)
              (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))) h) ∧
          (x ∉ Set.range P.i → IsEmpty (pullback (C := Scheme) P.i U.ι))) ∨
        (x ∉ P.x.smoothLocus ∧
          ∃ (c : Γ(Spec (.of V), B))
            (h : U.toScheme ⟶ (StrictSemistableModel.nodal c).scheme),
            Etale h ∧
            h ≫ (StrictSemistableModel.nodal c).baseMap ≫ hB.fromSpec = U.ι ≫ P.x ∧
            IsEmpty (pullback (C := Scheme) P.i U.ι))) := by
  sorry

end AlgebraicGeometry
