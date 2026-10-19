/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOriginEquation
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.ProperBasic
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CompactSupportSiteCoherence
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.KunnethDerivedTensorTEst
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.OpenTensorNormalization
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Etale-origin comparison of compact-support projection maps

Source: main-20261015 blueprint, sec-six-functors-basics/sk-prop-cohsm,
first paragraph of thm-pur-cohomological-smoothness.proof.md; Stacks Tags 0E48,
09AF and 0GL1 (blueprint: lem-pur-projection-comparison-etale-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- At positive finite coefficient level, the canonical compact-support site comparison
intertwines the two compactification projection maps on bounded constructible inputs,
with finite Tor amplitude only for H. The existential proofs record the bounded-below
domains of the two comparisons, rather than impose additional hypotheses. Naturality
in M,H is that of the specified bifunctor transformations and their natural inverses.
Source: main-20261015 blueprint, thm-pur-cohomological-smoothness.proof.md, paragraph 1;
Stacks Tags 0E48, 09AF, 0GL1
(blueprint: lem-pur-projection-comparison-etale-origin).

Proof:
1. The coefficient ring is finite. Choose a lower bound r for M and a Tor interval
   [a,b] for H. By lem-kun-0f1m take a flat-term K-flat model of H bounded below by a.
   Pullback preserves this model and its bound. Exact open extension preserves the
   lower bound r. By lem-kun-derived-tensor-t-est the two tensor inputs have lower
   bound a+r. Thus M and M tensor f*H lie in the domains of C.
2. On these flat K-flat models the canonical tensor and pullback comparisons agree
   on pure tensors, including the total differential signs and the j*p*=f* identity.
3. Apply lem-weil-pbc-ringed-exchange-tensor-coherence to the proper-factor site
   comparison square. Its exchange is the canonical counit mate fixed in
   lem-weil-pbc-comparison-direct-image-canonical-mate. This gives the proper square.
4. Extend lem-cbc-proetale-extension-zero-comparison termwise. Exactness on both sites
   makes it descend. Restrict the open tensor square back to X. Both routes become
   the identity tensor map by lem-sf-open-tensor-normalization and the pure-tensor
   formula for lem-pur-etale-open-derived-tensor. Full faithfulness of open extension
   proves the open square, without local freeness of M.
5. By lem-pur-compact-support-site-coherence, B=C inverse is exactly proper mate
   followed by proper image of the open comparison. Both projections are the proper
   counit mate followed by proper image of the corresponding open tensor map.
6. Paste the proper and open squares. Naturality of the proper mate at the open
   tensor arrow and naturality of projection in its first input give
   B_D V(PF-et) = PF-pro (B_M tensor 1) t inverse, with the specified target transport.
7. Precompose by t(C_M tensor 1), postcompose by C_D, and cancel inverse pairs.
   This is ProjectionComparisonEquation. All factors are natural in both inputs,
   so the equation is natural. Zero inputs, empty X and identity factors obey the
   same equations; smoothness and exceptional pullback are never used.
-/
theorem projectionComparison_etaleOrigin
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (H : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) X M)
    (_hH : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) Y H)
    (_hTor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing l E n) Y a b H) :
    projectionComparisonConclusion D l _hl E n f c M H _hM _hH _hTor := by
  sorry


end AlgebraicGeometry.ProEtale
