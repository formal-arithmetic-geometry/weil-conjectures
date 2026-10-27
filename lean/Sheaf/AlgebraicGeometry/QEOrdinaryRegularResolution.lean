/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.InvertibleCenter

/-! # Ordinary regular-functorial resolution of quasi-excellent rational schemes

Source: ILO, Travaux de Gabber, VIII Theorem 2.3.10, with 2.3.1, 2.3.4 and
Remark 2.3.5(i), printed pp. 91--93
(blueprint: lem-per-qe-ordinary-regular-resolution).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- There is one ordinary desingularization rule on all reduced Noetherian quasi-excellent
rational schemes, functorial for every regular morphism, including its ordered ideals,
identity and composition comparisons, the surjective clause and the empty-input convention.
Source: ILO VIII Theorem 2.3.10, 2.3.1, 2.3.4 and Remark 2.3.5(i), printed pp. 91--93
(blueprint: lem-per-qe-ordinary-regular-resolution).

Proof:
1. Fix the rule H of `lem-per-small-singular-locus-resolution`. Starting with the
length-zero R₀, use `lem-per-codimension-resolution-improvement` recursively on each
prefix to obtain one sequence R_d on the entire input category, including finite disjoint
unions. Its closed unresolved sets T_d decrease and avoid points of codimension at most d.
2. By `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, this decreasing family has
a minimal member T_N, so T_e = T_N for e ≥ N. If x belongs to T_N, choose an affine
Noetherian neighbourhood Spec A and its corresponding prime p. By
`lem-trf-noetherian-prime-finite-height`, chains ending at p have some finite bound h.
Primes of A_p are the primes contained in p, with the same inclusions, so the codimension
of x is at most h. For e ≥ max(N,h), membership in T_e contradicts its codimension bound.
Thus T_N is empty. This uses finite height at each point, not finite dimension of X.
3. Off T_N = ∅, codimension-resolution compatibility identifies all R_e, e ≥ N, with
R_N, preserving every ordered center. Choose the first such N and put F(X) = R_N(X).
The unresolved-set definition gives regular centers and regular final scheme; the same
codimension lemma supplies finite towers and coherent, nonempty, nowhere dense centers.
For the empty scheme R₀ already has empty unresolved set and length zero.
4. Given regular f : Y → X, use a common d at least both stabilization indices.
Codimension-resolution compatibility identifies F(Y) with the contraction of f*F(X),
including its ordered extended ideals. Flatness persists at every cartesian level by
`lem-weil-pbc-flat-morphism-base-change`; apply
`thm-nagata-blowup-flat-base-change` successively. An empty center has precisely the unit
ideal, and `cor-nagata-blowup-cartier-iso` makes its blowup an isomorphism. Remove exactly
these stages, retaining any nonempty Cartier center even when its blowup is an isomorphism.
5. Under two successive pullbacks, extending an ideal twice equals direct extension.
Unit ideals stay unit, so successive contractions retain exactly the same original ordered
indices as direct contraction. The maps of
`def-nagata-blowup-flat-base-change-map` send coefficients and fractions a/b on each
ordinary blowup chart to their images. For identities these are identity maps; for
composites these are the composite maps on all chart generators. They glue to the same
level maps. This proves both count and actual-map identity and composition laws.
6. If f is surjective, `lem-weil-pbc-surjective-base-change` makes every uncontracted
level map surjective. Applying the same result to each nonempty closed center shows its
inverse image is nonempty. Thus no extended ideal is unit, and no stage is deleted. -/
theorem exists_regular_functorial_qe_ordinary_resolution :
    Nonempty (RegularFunctorialQEOrdinaryResolution.{u}) := by
  sorry

end AlgebraicGeometry
