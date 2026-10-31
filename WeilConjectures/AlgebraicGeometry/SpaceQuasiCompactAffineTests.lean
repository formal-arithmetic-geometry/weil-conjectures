/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import WeilConjectures.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology

/-! # Quasi-compact algebraic-space morphisms: affine tests and locality

Source: Stacks Project, Morphisms of Spaces, Tags 03KG(1), (3), (6), 03HF and 03HD
(blueprint: lem-sfb-space-quasicompact-affine-tests).

The existing `IsQuasiCompactPresheafMap` is the affine-test atlas condition. The first
statement identifies it with the condition on all quasi-compact scheme tests in the node.
The other statements give Zariski locality, arbitrary algebraic-space base change, and
agreement with scheme-theoretic quasi-compactness for representable morphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Affine tests are equivalent to tests by every quasi-compact scheme; the source of each
pullback is quasi-compact precisely when it has a surjective étale quasi-compact scheme atlas.
Source: Stacks Project, Morphisms of Spaces, Tag 03KG(1), (3)
(blueprint: lem-sfb-space-quasicompact-affine-tests).

Proof: a test by an affine scheme is a quasi-compact scheme test, by
[lem-weil-pbc-affine-scheme-qcqs]. Conversely, cover a quasi-compact test scheme `T` by
finitely many affine opens, using [lem-weil-pbc-affine-opens-basis]. Their inclusions are
étale by [lem-weil-pbc-open-immersion-etale]. The affine-test hypothesis supplies a
quasi-compact scheme atlas over each of them. Fibre-product associativity from
[lem-trf-space-fibre-products-etale-covers] identifies these with the restrictions of
`X ×_Y T`. Apply [lem-trf-space-finite-qc-atlas-assembly] to assemble them into a
quasi-compact scheme atlas. For empty `T`, use the permitted empty finite cover.
The explicit atlas map here is equivalent to the compatible pair in the existing affine
predicate by the universal property of the presheaf pullback. -/
theorem quasiCompact_iff_quasiCompact_scheme_tests
    {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y) :
    IsQuasiCompactPresheafMap f.hom.hom ↔
      ∀ (T : Over S), CompactSpace T.left → ∀ h : yoneda.obj T ⟶ Y.obj.obj,
        ∃ (U : Over S) (a : yoneda.obj U ⟶ Limits.pullback f.hom.hom h),
          CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a := by
  sorry

/-- Quasi-compactness is equivalent to quasi-compactness over some Zariski open covering.
The covering is jointly surjective on points, and its members are the existing open
subspaces, whose inclusions are representable by open immersions.
Source: Stacks Project, Morphisms of Spaces, Tag 03KG(1), (6)
(blueprint: lem-sfb-space-quasicompact-affine-tests).

Proof: quasi-compactness is preserved by base change, so the one-member cover by `Y`
works. Conversely, pull the open covering back to an affine test scheme `V`. The
scheme tests of [def-a1-space-open-subspace] are open subschemes; they cover `V` by
[lem-a1-space-point-open-calculus]. Refine by affine opens using
[lem-weil-pbc-affine-opens-basis] and take a finite subcover using
[lem-weil-pbc-affine-scheme-qcqs]. Each affine member factors through a covering open,
so the corresponding pullback of `X` has a quasi-compact scheme atlas. Associativity in
[lem-trf-space-fibre-products-etale-covers] identifies those pullbacks with the pieces
of `X ×_Y V`. The finite étale cover and [lem-trf-space-finite-qc-atlas-assembly] give
an atlas of the whole pullback. No quasi-compactness of intersections is needed. -/
theorem quasiCompact_iff_exists_open_subspace_cover
    {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y) :
    IsQuasiCompactPresheafMap f.hom.hom ↔
      ∃ (I : Type (u + 1)) (U : I → OpenSubspace Y),
        IsJointlySurjective (fun i : I ↦ (U i).val.ι) ∧
          ∀ i : I, IsQuasiCompactPresheafMap
            (Limits.pullback.snd f.hom.hom (U i).val.ι) := by
  sorry

/-- Quasi-compact morphisms remain quasi-compact after any algebraic-space base change.
Source: Stacks Project, Morphisms of Spaces, Tag 03HF
(blueprint: lem-sfb-space-quasicompact-affine-tests).

Proof: for a quasi-compact scheme `T → Y'`, associativity of the sheaf fibre products
from [lem-trf-space-fibre-products-etale-covers] identifies
`(X ×_Y Y') ×_{Y'} T` with `X ×_Y T`. On sections the isomorphism deletes the redundant
`Y'` coordinate and its inverse inserts the image of `T`. Apply the quasi-compact
scheme-test criterion to `T → Y' → Y`; its atlas transports across this isomorphism.
This requires no representability, separation, or finiteness hypothesis on `g`. -/
theorem quasiCompact_presheafMap_baseChange
    {S : Scheme.{u}} (X Y Y' : AlgebraicSpace S) (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : IsQuasiCompactPresheafMap f.hom.hom) :
    IsQuasiCompactPresheafMap (Limits.pullback.snd f.hom.hom g.hom.hom) := by
  sorry

/-- For a representable map, quasi-compactness is exactly quasi-compactness of its scheme
base changes. `IsRepresentableWith` supplies each representing pullback square and the
scheme quasi-compactness of its projection; the property is invariant under the unique
isomorphism between any two representing squares.
Source: Stacks Project, Morphisms of Spaces, Tag 03HD
(blueprint: lem-sfb-space-quasicompact-affine-tests).

Proof: every scheme base change is a scheme by representability in
[def-trf-algebraic-space]. On schemes, [lem-a1-space-etale-open-image] and
[def-a1-space-point-topology] identify having a quasi-compact scheme atlas with ordinary
quasi-compactness. If `f` is quasi-compact, test on each affine open `W` of a test scheme
`T`. By [lem-weil-pbc-affine-scheme-qcqs] and fibre-product associativity, the inverse
image of `W` under the representing scheme projection is quasi-compact. This is the
scheme condition in [def-weil-finite-type-morphism]. Conversely, if each representing
projection is quasi-compact, apply [lem-weil-pbc-quasi-compact-morphism-preimage-qc-open]
to the whole of each quasi-compact `T`. Its inverse image is the entire representing
scheme, so its quasi-compactness gives the required atlas of `X ×_Y T`. -/
theorem quasiCompact_iff_representableWith_quasiCompact
    {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (hf : IsRepresentable f.hom.hom) :
    IsQuasiCompactPresheafMap f.hom.hom ↔
      IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) f.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
