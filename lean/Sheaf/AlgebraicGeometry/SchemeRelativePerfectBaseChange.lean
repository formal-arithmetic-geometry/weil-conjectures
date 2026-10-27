/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.Algebra.Homology.RingedTorAmplitudeStalkTest
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import Sheaf.AlgebraicGeometry.AffineRelativeTorAmplitudeCriterion
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.AlgebraicGeometry.AffineKFlatPullbackChartComparison
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryIso
import WeilConjectures.Algebra.Homology.TorAmplitudeFlatModel
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Mathlib.RingTheory.Flat.Stability
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Relative perfection under arbitrary base change of schemes

Source: Stacks Project, perfect.tex, Tag 0DI5, lemma-base-change-relatively-perfect,
with relative perfection as in Tag 0DI0, definition-relatively-perfect
(blueprint: lem-sfb-scheme-relative-perfect-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Relative perfection survives arbitrary base change of a flat locally finitely
presented morphism. Finite relative Tor dimension is required on a neighbourhood of
each point; the intervals need not be uniform on the scheme.

Source: Stacks Project, perfect.tex, Tags 0DI0 and 0DI5
(blueprint: lem-sfb-scheme-relative-perfect-base-change).

Proof:
1. Around a point of the fibre product choose affine charts U = Spec A in X,
   V = Spec R in S and V' = Spec R' in S', with U and V' mapping into V.
   Their fibre product U' = Spec (A ⊗[R] R') is an open neighbourhood, by
   lem-weil-pbc-affine-opens-basis, lem-weil-pbc-open-fibre-product and
   lem-weil-pbc-fibre-product-affine-spectra. The local relative Tor interval
   restricts to U by lem-trf-ringed-tor-amplitude-stalk-test.
2. The affine adjunction (lem-a1-locally-ringed-space-affine-adjunction),
   lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-spec-map-stalk-localization identify the stalk maps of f with
   R_p → A_q. Flatness and lem-pc-affine-sections-flat-over-base imply R → A
   is flat. By lem-sc-pseudo-coherent-qcoh,
   lem-pc-affine-qcoh-derived-equivalence and lem-pc-affine-pseudo-coherent-criterion,
   E on U has a bounded-above finite-free A-model Q. By
   lem-trf-affine-relative-tor-amplitude-criterion, after shrinking U around the
   point if necessary, its underlying R-complex has a finite Tor interval [a,b].
3. Q is K-flat over both A and R by lem-pc-module-bounded-flat-kflat.
   By lem-pc-affine-kflat-pullback-chart-comparison its affine derived pullback
   is represented by Q' = (A ⊗[R] R') ⊗[A] Q, still bounded above and finite free.
   Thus lem-pc-affine-pseudo-coherent-criterion gives pseudo-coherence.
4. By lem-pc-base-tensor-ordinary-iso, the underlying R'-complex of Q' is
   R' ⊗[R] Q. Choose a bounded flat R-model F in [a,b] using
   lem-pc-module-tor-amplitude-flat-model. The functor of
   lem-pc-derived-tensor-second-factor-functor transports the isomorphism of
   these K-flat models to D(R'). Every term of R' ⊗[R] F is flat by
   lem-weil-pbc-flat-module-base-change, and it vanishes outside [a,b]. Hence
   lem-pc-module-tor-amplitude-flat-model gives the same interval over R'.
5. Apply lem-trf-affine-relative-tor-amplitude-criterion and the stalk test
   to recover the relative interval over S'. The composition isomorphism of
   lem-pc-ringed-spaces-derived-pullback-composition identifies the affine
   calculation with restriction of the global derived pullback. These opens
   cover the fibre product, giving both asserted local properties. No flatness
   of g is used. Empty schemes have a vacuous cover; the zero complex uses [0,0]. -/
theorem relativePerfect_baseChange
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (g : S' ⟶ S) (E : schemeDerivedCategory X)
    (hE : IsPseudoCoherent X E)
    (hTor : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      HasFiniteTorDimensionOver (U.ι ≫ f) ((derivedPullback U.ι).obj E)) :
    IsPseudoCoherent (pullback f g) ((derivedPullback (pullback.fst f g)).obj E) ∧
      ∀ x' : (pullback f g : Scheme.{u}), ∃ U' : (pullback f g : Scheme.{u}).Opens,
        x' ∈ U' ∧ HasFiniteTorDimensionOver (U'.ι ≫ pullback.snd f g)
          ((derivedPullback U'.ι).obj ((derivedPullback (pullback.fst f g)).obj E)) := by
  sorry

end AlgebraicGeometry.Scheme
