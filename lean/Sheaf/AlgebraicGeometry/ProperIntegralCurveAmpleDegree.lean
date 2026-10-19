/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Field.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import Sheaf.AlgebraicGeometry.AffineCapSectionOpen
import Sheaf.AlgebraicGeometry.AffineComplementFiniteOnIntegralCurve
import Mathlib.AlgebraicGeometry.FunctionField
import Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity
import Sheaf.TraceFormula.IdealTwistVanishingImpliesAmple
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive

/-!
# Positive degree characterizes ampleness on a proper integral curve

Source: Stacks Project, Varieties, Tag 0B5X, lemma-ample-curve
(blueprint: lem-trf-proper-integral-curve-ample-degree).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- On a proper integral curve over a field, an invertible module is ample exactly when its
cohomological degree is positive. No smoothness or geometric integrality is assumed.

Source: Stacks Project, Varieties, Tag 0B5X, lemma-ample-curve (applied to a proper integral
curve).

Proof, following the node's nine steps:
1. Integrality gives nonemptiness. Properness gives finite type and separatedness, hence a
   variety (`def-pc-curve`). A field is Noetherian; finite type over it makes C Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`). Its structure sheaf and invertible modules are
   coherent by `pqf-lem-coherent-ft-locnoeth` and local freeness of rank one.
2. Put d = deg(N). The tensor unit has degree zero; induction using
   `lem-trf-curve-degree-tensor-additive` gives deg(N^n) = nd for all n >= 0, so
   chi(N^n) = nd + chi(O_C), by `def-pc-degree-line-bundle`.
3. If N is ample, global functions form a finite field extension of k
   (`lem-pc-h0-proper-variety`). C cannot be affine: it would be the spectrum of that field,
   contradicting dimension one. At a chosen point ampleness supplies a positive tensor power
   and nonzero section s with affine C_s. Thus C_s is proper in C; applying
   `lem-trf-curve-section-degree-positivity` gives nd > 0 and therefore d > 0.
4. Conversely assume d > 0. Cohomology is finite-dimensional (`lem-pc-coherent-hi`) and
   vanishes above degree one (`lem-sc-noetherian-cohomology-above-dimension`). Hence
   h^0(N^n) >= nd + chi(O_C). Choose a nonempty affine open U. Its complement is finite
   (`lem-sc-affine-complement-finite-on-integral-curve`). The boundary points are closed:
   a non-generic nonclosed point would give a length-two chain of irreducible closed sets,
   using `lem-weil-pbc-scheme-sober`. Their residue fields are finite over k by
   `lem-kun-closed-point-field`.
5. Choose n >= 1 with h^0(N^n) greater than the sum of these residue-field degrees.
   Evaluation at the boundary has a nonzero kernel since N^n has rank-one fibres. A nonzero
   section s in that kernel has C_s contained in U, and C_s is affine by
   `lem-sc-affine-cap-section-open`. No surjectivity of evaluation is needed.
6. For a quasi-coherent ideal I, coherence follows from
   `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`. Put F_e = I tensor N^(en).
   The nonzero s is nonzero at the generic point and at every stalk, by
   `lem-sc-integral-scheme-stalks-in-function-field`. On each stalk its multiplication on
   the ideal is injective, since the local ring is a domain. It is an isomorphism on C_s.
   Thus 0 -> F_e -> F_(e+1) -> Q_e -> 0 is exact with coherent Q_e supported outside C_s.
   This support has dimension at most zero by the dimension-one hypothesis.
7. `lem-pc-chi-zero-dim-support` gives H^1(Q_e) = 0. The long exact sequence of
   `pqf-def-cohomology` makes H^1(F_e) -> H^1(F_(e+1)) surjective. Its composites give
   surjections H^1(I) -> H^1(F_e).
8. H^1(I) is finite-dimensional (`lem-pc-coherent-hi`). Every basis element is killed by
   some power of s, by `lem-sc-section-affine-open-kills-cohomology`; its qcqs hypotheses
   follow from Noetherianity and `lem-weil-pbc-locally-noetherian-quasi-separated`.
   Choose E >= 1 at least all these exponents (E = 1 for the zero vector space).
   The surjection H^1(I) -> H^1(F_E) is zero, so H^1(I tensor N^(En)) = 0.
9. This holds for every quasi-coherent ideal I, with positive exponent En. Since k is
   Noetherian and C is proper, `lem-trf-ideal-twist-vanishing-implies-ample` implies absolute
   ampleness. Combining this with step 3 proves the equivalence without smoothness or
   geometric integrality.
(blueprint: lem-trf-proper-integral-curve-ample-degree)
-/
theorem proper_integral_curve_isAmple_iff_degree_pos
    {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
    [IsIntegral C] [IsProper (C ↘ Spec (.of k))]
    (hdim : topologicalKrullDim C = (1 : WithBot ℕ∞))
    (N : C.Modules) [N.IsInvertible] :
    Scheme.Modules.IsAmple C N ↔ 0 < Scheme.Modules.degree k N := by
  sorry

end AlgebraicGeometry.Scheme.Modules
