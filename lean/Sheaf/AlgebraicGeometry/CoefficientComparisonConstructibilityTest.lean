/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData
/-! # The stratum test for coefficient-sized comparison
Source: blueprint constructible comparison, Stacks Tag 09AK.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- Canonical inverse image preserves and reflects constructibility of etale modules.
This is a property test on a given etale module, without an essential-surjectivity
claim or a derived assertion.
Source: blueprint sk-thm-pe-constructible-comparison, equivalence part;
finite-local-system comparison, Stacks Tag 09AK
(blueprint: lem-pe-coefficient-comparison-constructibility-test).

Proof: inverse image commutes with restriction to each locally closed stratum by
the comparison base-change mate. An etale finite local trivialization pulls back
to a pro-etale trivialization with the same finite module. Conversely, a finite
pro-etale local system descends uniquely to the etale site: finite presentation
over the Noetherian ring lets its trivializations and transition maps descend
along affine pro-etale presentations to etale finite stages. Fully faithful
comparison on each stratum identifies that descended system with the restriction
of the given etale module. The same finite partition thus witnesses etale
constructibility. Affine-local finite partitions glue on each quasi-compact affine
open, and arbitrary schemes are covered by such opens. Constant-scalar restriction
and the coefficient-sized site equivalences preserve covers, the constant finite
models and the stratum inverse images. No quasi-compactness assumption on the
whole scheme is needed. The empty scheme has the empty partition, and the zero
module is covered by the zero finite model, so the two tests also agree there. -/
theorem coefficientComparison_constructibilityTest (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ∀ G : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
      Scheme.IsCoefficientConstructibleEtaleModule X A G ↔
        Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
          ((constructibleComparisonPullback X A).obj G) := by sorry
end AlgebraicGeometry.ProEtale
