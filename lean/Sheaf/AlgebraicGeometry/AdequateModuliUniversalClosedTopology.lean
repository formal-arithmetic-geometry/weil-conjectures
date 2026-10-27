/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
import Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus
import Sheaf.AlgebraicGeometry.StackPointTopology

/-! # Universal closedness and surjectivity of adequate moduli spaces

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Theorem 5.3.1(1),(2), with Proposition 5.2.9(3) and Lemma 5.2.11
(blueprint: lem-sfb-adequate-moduli-universal-closed-topology).

The target point space is that of the discrete groupoid represented by the test scheme.
Its canonical residue-field identification with the scheme's Zariski space is the last
clause of `stack_point_topology`. The source has the existing smooth-atlas topology.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Every scheme base change of an adequate moduli morphism is a closed surjection
on point spaces. The projection is the actual second projection of the 2-fibre product;
the test map is an arbitrary morphism from the representable presheaf of a scheme.
Source: Alper, Theorem 5.3.1(1),(2), printed p.511, Proposition 5.2.9(3), and
Lemma 5.2.11 (blueprint: lem-sfb-adequate-moduli-universal-closed-topology).

Proof, following the three steps of the DAG node:
1. First prove surjectivity for any adequate map U → V. Represent a point of V
by Spec L. The factorization in lem-sfb-adequate-base-change-affinization has an
adequate map U_L → H = Spec B and a homeomorphism |H| → |Spec L|. Thus B is
nonzero (def-weil-affine-spectrum). Condition (1) of def-sfb-adequate-moduli-space,
using the direct image of def-sfb-stack-quasi-coherent-algebra, identifies B with
the global functions on U_L. If U_L had no points, an atlas would be empty and
its global functions would be the zero ring. This contradiction supplies a point
above the chosen point of V. All fibre products are algebraic by
lem-sfb-algebraic-stack-fibre-products.
2. By lem-sfb-smooth-presentation-closed-subsets, a closed subset of |U| is the
support of a reduced closed substack Z. By lem-sfb-adequate-closed-substack-affinization,
the map from Z factors through an adequate map Z → E, a homeomorphism |E| → |W|,
and a closed immersion W → V. Step 1 makes Z → E surjective on points. Its image
in V is therefore exactly |W|, closed by lem-sfb-stack-closed-immersion-calculus.
3. For the arbitrary test scheme T, lem-sfb-adequate-base-change-affinization factors
U ×_V T → T as an adequate map followed by a homeomorphism on points. Steps 1
and 2 apply to the first map. A homeomorphism is surjective and closed, so their
composite has both properties. This includes the empty scheme and does not assert
that the base-changed projection itself is adequate. -/
theorem adequateModuli_universal_closed_topology {k : Type u} [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (Y : AlgebraicSpace (Spec (CommRingCat.of k)))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (hφ : IsAdequateModuliSpace F hF Y φ) :
    ∀ (T : Over (Spec (CommRingCat.of k))) (t : yoneda.obj T ⟶ Y.obj.obj),
      Function.Surjective (moduliPointMap (moduliTwoFiberSnd φ (discreteModuliMap t))) ∧
        IsClosedMap (moduliPointMap (moduliTwoFiberSnd φ (discreteModuliMap t))) := by
  sorry

end CategoryTheory
