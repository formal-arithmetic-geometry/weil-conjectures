/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Sheaf.AlgebraicGeometry.GroupoidScheme
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Sheaf.AlgebraicGeometry.PerfectFieldGroupoidImageClosure
import Sheaf.AlgebraicGeometry.ConstantGroupSchemeMultiplication

/-! # Density of prime-to-characteristic torsion in an abelian variety

Source: Milne, Abelian Varieties (2008), I Section 10, pp.42-45; Milne, Abelian
Varieties (January 2, 2022), Section 12, first unnumbered lemma after Proposition 12.1,
printed p.19 (blueprint: lem-sfb-abelian-prime-to-torsion-dense).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every closed subset containing the images of all prime-to-characteristic torsion
rational points of an abelian variety is the whole underlying space. This includes the
zero-dimensional abelian variety. The point of `Spec F` is unique, hence `default`.

Source: Milne, Abelian Varieties (2022), Section 12, first unnumbered lemma after
Proposition 12.1, printed p.19; supporting torsion counts: Milne, Abelian Varieties
(2008), Theorem 7.2 and Remark 7.3, pp.33-34.
(blueprint: lem-sfb-abelian-prime-to-torsion-dense)

Proof:
1. By lem-sc-av-commutative the rational points form an abelian group. The union T of
all n-torsion for positive n nonzero in F is a subgroup: 0 is killed by 1, and if
nx = my = 0, then nm(x-y) = 0. Form its constant group scheme by
lem-weil-pbc-scheme-coproduct-family and
lem-weil-pbc-constant-group-scheme-multiplication. Evaluation on each component
Spec F gives a group homomorphism to B with topological image T.
2. View these group schemes as groupoids on Spec F (def-a1-groupoid-scheme).
The algebraically closed field F is perfect. Apply
lem-sfb-perfect-field-groupoid-image-closure to evaluation: the closure of T has
a reduced closed subgroup scheme structure H. It is finite type, since it is a
closed subscheme of the finite type scheme B (def-weil-finite-type-morphism).
3. By lem-sfb-abelian-closed-subgroup-reduced-component its identity component C
is an abelian variety and a closed subgroup of B. By
lem-sfb-group-neutral-component-translates, H has finitely many components, each
a rational translate of C. Write r for their positive number. By
lem-kun-dimension-finite-type and def-kun-topological-krull-dimension, the dimensions
g of B and h of C are finite nonnegative integers and h is at most g.
4. Choose a prime ell invertible in F (2 unless the characteristic is 2, then 3).
For every m at least 1, put N = ell^m. By lem-sc-ntorsion-etale, B[N](F) and C[N](F)
have N^(2g) and N^(2h) elements. All B[N](F) lie in H. In each component containing
such a point x, subtraction of x injects its N-torsion points into C[N](F).
Consequently N^(2g) is at most r times N^(2h).
5. If h < g, cancellation gives ell^(2m(g-h)) at most r for every m. At m = r+1,
this contradicts ell^(2m(g-h)) at least 2^m at least m+1. Hence h = g.
6. By lem-sc-abelian-variety-characterization, B is irreducible. If its closed
subset C were proper, a maximal chain in C would extend by B, contradicting equal
finite dimensions (def-kun-topological-krull-dimension). Thus C is all of B as a
set, so the closure of T is B, and every closed subset containing T is B.
For g = 0, h is already 0 and the same chain argument applies. -/
theorem IsAbelianVariety.eq_univ_of_contains_primeToTorsion
    (F : Type u) [Field F] [IsAlgClosed F]
    (B : Over (Spec (.of F))) [GrpObj B] [IsAbelianVariety B]
    (Z : Set B.left) (hZ : IsClosed Z)
    (hT : ∀ (n : ℕ), 0 < n → (n : F) ≠ 0 →
      ∀ q : (torsionSubgroupScheme B n).hom.fieldPoints F,
        (torsionSubgroupScheme.ι B n).left (q.1.base default) ∈ Z) :
    Z = Set.univ := by
  sorry

end AlgebraicGeometry
