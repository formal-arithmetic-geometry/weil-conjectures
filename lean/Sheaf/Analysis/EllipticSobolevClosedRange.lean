/-
Copyright (c) 2026 The Weil SHEAF project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil SHEAF project
-/
module

public import Sheaf.Analysis.EllipticSobolevData
import Sheaf.Analysis.CompactRemainderCoercivity
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Closed range of an elliptic Sobolev realization

Source: Demailly, Complex Analytic and Differential Geometry, VI §1 (1.4), VI §2
Corollary (2.4)(ii), equations (2.5)–(2.6), printed pp.288–290
(blueprint: lem-sfb-elliptic-sobolev-closed-range).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped Manifold ContDiff

namespace EllipticSobolev

/-- The integrated and Sobolev Hilbert completions have their measurable and distributional
realizations, and an elliptic operator has a unique bounded extension with closed range.
Uniqueness is asserted among all bounded extensions of the smooth operator, before imposing
its distributional equation or its closed range. The local test identities give the actual
variable-coefficient distributional differential operator.

Source: Demailly, Complex Analytic and Differential Geometry, VI §1 (1.4), VI §2 before
(2.1), and the closed-range part of Corollary (2.4)(ii), pp.288–290
(blueprint: lem-sfb-elliptic-sobolev-closed-range).

Proof plan, following the five DAG steps:
1. Apply lem-sfb-bundle-sobolev-rellich to both metric bundles, with s = k. This constructs
   the Hilbert completions, dense smooth maps, measurable realization and injective maps
   into local distributions. The inclusion J from the source Sobolev space to L2 is compact.
2. Refine the finite atlas to trivialize both bundles. Equivalent localization norms from
   lem-sfb-bundle-sobolev-rellich let us use this refinement. Bounded coefficients on the
   finitely many compact supports bound the L2 norm of Qs by M times the Sobolev norm of s.
   Apply lem-sfb-dense-subspace-contractive-extension to Q/M and rescale. Density proves
   uniqueness among continuous linear extensions.
3. Approximate u by smooth sections in the Sobolev norm. Every localized derivative through
   order k converges in L2. Multiplication by the local coefficients preserves this limit.
   Test against compactly supported smooth functions, use Cauchy–Schwarz, and integrate by
   parts to identify the bounded extension with the distributional differential expression.
4. Extend lem-sfb-elliptic-global-garding-estimate from smooth sections by density and norm
   continuity. Apply lem-sfb-compact-remainder-coercivity with the compact inclusion J to
   obtain a uniform bound on the Sobolev orthogonal complement of the extension's kernel.
5. The kernel is closed. Use lem-sfb-hilbert-orthogonal-projection to replace preimages of
   a convergent sequence in the range by their kernel-orthogonal components. The estimate
   makes these components Cauchy. Completeness gives a limit, and continuity maps that
   limit to the prescribed range limit. The metric sequential criterion proves closedness. -/
theorem exists_elliptic_sobolev_closed_range
    (m r k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (N : Type u) [TopologicalSpace N] [ChartedSpace (Model m) N]
    [IsManifold (𝓘(ℝ, Model m)) ∞ N] [T2Space N] [CompactSpace N]
    [MeasurableSpace N] [BorelSpace N]
    (d : Base m N) (G H : MetricBundle.{u, v} m r N)
    (Q : EllipticOperator G H k) (aG : Localization G) (aH : Localization H) :
    ∃ (LG : L2Model d G) (LH : L2Model d H)
      (SG : SobolevModel aG k LG) (_ : SobolevModel aH k LH),
      ∃ T : SG.space →L[ℝ] LH.space,
        (∀ s : Sections G, T (SG.ofSmooth s) = LH.ofSmooth (Q.op s)) ∧
        (∀ T' : SG.space →L[ℝ] LH.space,
          (∀ s : Sections G, T' (SG.ofSmooth s) = LH.ofSmooth (Q.op s)) → T' = T) ∧
        (∀ u : SG.space, DistributionalEquation Q LG LH (SG.toL2 u) (T u)) ∧
        IsClosed (Set.range T) := by
  sorry

end EllipticSobolev
