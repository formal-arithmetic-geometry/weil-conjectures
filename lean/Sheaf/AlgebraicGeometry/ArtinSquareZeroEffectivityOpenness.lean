/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion
public import Sheaf.AlgebraicGeometry.ArtinSquareZeroGluing
public import Sheaf.AlgebraicGeometry.ArtinStrongSquareZeroEffectivity
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.Thickening

/-! # Strong square-zero effectivity and openness of versality

Source: Stacks Project, artin.tex, Tag 0CXU (lemma-SGE-implies-openness-versality),
remark-strong-effectiveness and definition-RS-star, over Spec Z
(blueprint: lem-sfb-artin-square-zero-effectivity-openness).

The total-category formulation retains all arrows and the specified reduction
isomorphisms. The existing ArtinCriterion definitions supply directed-limit
preservation and the Artinian lifting definition of openness of versality.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ArtinCriterion

/-- Strong square-zero effectivity implies openness of versality. The diagonal,
(RS*), limit preservation, and effectivity are the four hypotheses of the source;
no stack descent or effectivity over arbitrary complete local rings is assumed.

Source: Stacks Project, artin.tex, Tag 0CXU
(blueprint: lem-sfb-artin-square-zero-effectivity-openness).

Proof:
1. Restrict U to an affine finite type neighbourhood of the given versal point u0.
By lem-weil-pbc-finite-type-over-noetherian this is Noetherian. If no required
neighbourhood exists, u0 is in the closure of the nonversal finite type locus E.
2. Lem-sfb-artin-versality-generalization excludes specializations from E to u0.
Lemma lem-sfb-noetherian-countable-antichain gives an infinite countable subset
with the same closure and no specializations; enumerate it without repetitions.
3. Apply lem-sfb-artin-nonversal-thickening-tower. Every transition kernel is
square zero since it lies in the square-zero kernel over R0. Strong effectivity,
with indices shifted by one, gives an object over the inverse limit ring R.
4. The projection R to R0 is surjective by successive lifts and has square-zero
kernel coordinatewise. The finitely generated integer subalgebras of R form a
directed union. Use lem-weil-pbc-directed-subalgebra-ring-colimit and
lem-weil-pbc-limit-affine-transition, then limit preservation, to descend the
object to a finite type subalgebra R' of R.
5. Adjoin finitely many lifts of generators of R0 to R'. The resulting map to
R0 is surjective with square-zero kernel. This gives a first order thickening
U into U' and compatible identifications with all the tower objects.
6. Apply lem-sfb-artin-versal-base-change-smooth to the isomorphism algebraic
space Z for x and the descended object. It is smooth over U' on an open O
containing the image of u0 under the section i of Z over U.
7. Choose a principal open V around u0 inside the inverse image of O. Lift its
defining function to R' to obtain V'. Localization preserves the square-zero
surjective quotient. Lem-sfb-smooth-space-affine-infinitesimal-lift lifts i on
V to a section over V', using def-sbc-first-order-thickening.
8. Project this section to U and pull back the universal isomorphism. Some
nonversal point in the enumerated set lies in V. Pulling back to its tower
stage gives a local retraction extending the prescribed reduction isomorphism.
The reduction is the identity because its factors are the chosen isomorphism
and its inverse. This contradicts lem-sfb-artin-nonversal-thickening-tower.
Hence the required open neighbourhood exists. -/
theorem opennessOfVersality_of_strongSquareZeroEffectivity
    (F : BasedCategory.{v, w} (Over Base.{u}))
    (hFibred : IsFibredInGroupoids F)
    (hDiagonal : HasAlgebraicSpaceDiagonal F)
    (hGluing : SquareZeroGluing F)
    (hLimits : IsLimitPreserving F)
    (hEffective : StrongSquareZeroEffectivity F) : OpennessOfVersality F := by
  sorry

end AlgebraicGeometry.ArtinCriterion
