/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.SpaceFibreProductComparison
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteComposition
import Sheaf.AlgebraicGeometry.SpaceSeparatedLqfPermanence
import Sheaf.AlgebraicGeometry.AdmissibleFreeFiniteQuotient
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Schematic strata covering quasi-compact field points

Source: Stacks Project, Decent Spaces, Tag 0BBN (lemma-filter-quasi-compact),
clauses (1) and (2) (blueprint: lem-sfb-qc-space-schematic-strata).

The natural-number index `p` denotes the source's index `p + 1`.
The schemes `T p` themselves represent the reduced closed differences;
no finite termination or quasi-separatedness is asserted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact algebraic space has a decreasing open filtration with reduced
schematic differences covering every point with a quasi-compact field representative.
Closedness and quasi-compactness of a field map are tested on every scheme base change.

Source: Stacks Project, Decent Spaces, Tag 0BBN (lemma-filter-quasi-compact),
clauses (1) and (2) (blueprint: lem-sfb-qc-space-schematic-strata).

Proof:
1. The quasi-compact atlas makes the point space quasi-compact by
lem-a1-space-point-open-calculus. Choose an affine surjective etale atlas A -> X by
lem-sfb-qc-space-affine-etale-atlas. All absolute products below are over Spec Z.
2. The absolute diagonal of A is closed. The relative diagonal of A -> X is its
scheme-test base change, hence closed by lem-weil-pbc-affine-source-morphism-separated
and lem-weil-pbc-closed-immersion-base-change. It is also open by
lem-sfb-space-separated-etale-diagonal-complement.
3. Form the p-fold fibre product for positive p and remove all pairwise equality loci.
Each equality locus is open and closed by step 2. The remaining scheme W_p is separated
and etale over X, by lem-trf-space-representable-etale-scheme-tests,
lem-sfb-space-separated-fp-composition and lem-weil-pbc-etale-composition-cancellation.
For p = 1 it is A itself.
4. Regard the spaces over Spec Z using lem-sfb-space-change-base-to-integers.
Inductively compare the fibre product to the absolute product of p copies of A.
The comparison is separated locally quasi-finite by lem-sfb-space-fibre-product-comparison,
lem-a1-etale-space-locally-quasi-finite, lem-weil-pbc-separated-lqf-base-change,
lem-a1-scheme-lqf-composition and lem-sfb-space-separated-fp-composition.
The target is affine by lem-weil-pbc-fibre-product-affine-spectra. Restriction to W_p
preserves these properties by lem-a1-space-separated-lqf-permanence. Every finite set in
W_p therefore lies in an affine open by lem-sfb-separated-lqf-affine-finite-set.
5. The symmetric group acts freely on W_p by permuting distinct coordinates. A nonidentity
permutation fixing a tuple would force an equality locus; this also holds piecewise for
locally constant permutations on disconnected tests. Every orbit is finite. Apply
lem-sfb-admissible-free-finite-quotient to obtain a separated scheme V_p and a finite
surjective etale quotient W_p -> V_p. The invariant map to X descends, using the
change-of-base equivalence of lem-sfb-space-change-base-to-integers. Geometric points of
V_p are permutation orbits of geometric points of W_p.
6. The descended map V_p -> X is representable. On each scheme test it is etale by
lem-sfb-scheme-etale-source-target-properties, using the surjective etale source cover
W_p -> V_p and lem-trf-space-representable-etale-scheme-tests. Its open image U_p and
surjective etale factorization come from lem-a1-etale-scheme-map-open-image.
7. Over an algebraically closed field the atlas fibre is a discrete union of field
spectra by lem-weil-pbc-etale-fibre-discrete-separable-points. If I indexes its components,
the fibre of W_p consists of ordered distinct p-tuples in I. The quotient formula of
lem-sfb-admissible-free-finite-quotient identifies the fibre of V_p with p-element subsets.
8. Thus U_p consists precisely of points whose geometric atlas fibre has at least p
points. This gives decreasing opens and U_1 = X, using surjectivity of A -> X and
lem-a1-space-point-open-calculus. No bound on fibre size is needed.
9. Give U_p minus U_(p+1) its reduced closed structure by
lem-sfb-space-reduced-closed-support. Its pullback Z_p to V_p is a scheme, closed in V_p,
and surjective etale over the closed subspace. Every geometric fibre has one point,
since I has exactly p elements and exactly one p-element subset.
10. The map V_p -> U_p is separated: its relative diagonal is a base change of the
absolute closed diagonal of the separated scheme V_p. By closed-immersion base change
and lem-sfb-space-separated-fp-composition the same holds for Z_p -> T_p. Apply
lem-sfb-space-separated-etale-diagonal-complement to obtain Z_p isomorphic to T_p.
Consequently the reduced closed subspace is represented by a reduced scheme, and its
point map identifies its points with the stated difference.
11. For a quasi-compact field representative, its atlas pullback E -> A is quasi-compact.
Since A is affine, E is quasi-compact. Its map to the field spectrum is quasi-compact,
and remains so over an algebraic closure, by lem-sfb-space-quasicompact-affine-tests,
lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-qcqs-morphism-permanence.
The discrete etale fibre has finitely many components by
lem-weil-pbc-etale-fibre-discrete-separable-points. Their number p is positive by
surjectivity of A -> X, so the representative belongs to T_p by step 8. For empty X
there are no field representatives and all strata can be empty. -/
theorem exists_schematic_strata_of_quasiCompact_atlas
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : ∃ (A : Over S) (a : yoneda.obj A ⟶ X.obj.obj),
      CompactSpace A.left ∧ IsRepresentable a ∧ IsSurjective a ∧ IsEtale a) :
    ∃ (U : ℕ → OpenSubspace X) (T : ℕ → Over S)
      (i : ∀ p : ℕ, yoneda.obj (T p) ⟶ (U p).val.toFunctor),
      (U 0).val = ⊤ ∧
      (∀ p : ℕ, U (p + 1) ≤ U p) ∧
      (∀ p : ℕ, AlgebraicGeometry.IsReduced (T p).left ∧
        IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left) (i p) ∧
        Function.Injective (schemePointMap (i p ≫ (U p).val.ι)) ∧
        Set.range (schemePointMap (i p ≫ (U p).val.ι)) =
          pointImage (U p).val.ι \ pointImage (U (p + 1)).val.ι) ∧
      (∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
        (x : X.obj.obj.obj (op (Over.mk s))),
        IsRepresentableWith (fun _ _ f ↦ QuasiCompact f.left) (yonedaEquiv.symm x) →
          ∃ p : ℕ, Quot.mk _ (PointRepresentative.mk K s x) ∈
            Set.range (schemePointMap (i p ≫ (U p).val.ι))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
