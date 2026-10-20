/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import Sheaf.AlgebraicGeometry.CartierDivisorFinite
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme

/-!
# Degree positivity from a section on a proper integral curve

Source: Stacks Project, Varieties, Tag 0B40, clauses (1) and (2), and Tag 0AYY
(blueprint: lem-trf-curve-section-degree-positivity).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A nonzero global section of an invertible module on a proper integral curve has
nonnegative degree; if its nonvanishing locus is not the whole curve, its degree is positive.

Source: Stacks Project, Varieties, Tag 0B40, clauses (1) and (2), using Tag 0AYY
(blueprint: lem-trf-curve-section-degree-positivity).

Proof:
1. Form the zero scheme D of s (def-pc-zero-scheme). By the local zero-scheme description
   (lem-pc-zero-scheme-properties), its support is the complement of the nonvanishing locus
   (def-weil-pbc-ample-invertible-module). Since C is integral and s is nonzero,
   lem-pc-nonzero-section-integral-cartier makes D an effective Cartier divisor. Thus D is
   nonempty precisely when the nonvanishing locus is not all of C.
2. Apply lem-pc-zero-scheme-divisor-iso to the section morphism O_C -> L to obtain
   L isomorphic to O_C(D). The degree definition (def-pc-degree-line-bundle) is invariant
   under isomorphism, so these two modules have the same degree.
3. Convert topological dimension one to the local-ring dimension convention using
   lem-pc-scheme-dimension-local-rings and def-pc-dimension. The effective-divisor clause of
   lem-pc-degree-base-change identifies the degree of O_C(D) with dim_k Gamma(D, O_D),
   and this vector space is finite-dimensional.
4. Its dimension is nonnegative. If D is nonempty, lem-pc-cartier-divisor-finite-over-field
   makes D affine and finite over k. The algebra Gamma(D, O_D) is then nonzero, since an
   affine nonempty scheme has a nonzero coordinate ring. Its finite vector-space dimension
   is positive, giving the second assertion.
-/
theorem curve_section_degree_nonneg_and_pos (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] [IsIntegral C]
    [IsProper (C ↘ Spec (.of k))] (hC : topologicalKrullDim C = 1)
    (L : C.Modules) [L.IsInvertible] (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    0 ≤ L.degree k ∧ (nonvanishingLocus L s ≠ Set.univ → 0 < L.degree k) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
