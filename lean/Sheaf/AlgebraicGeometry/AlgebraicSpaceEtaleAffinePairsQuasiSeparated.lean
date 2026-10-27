/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! # Affine étale pairs test absolute quasi-separatedness

Source: Stacks Project, Properties of Spaces, Tag 0AHR, proof of (3) implies (1);
Decent Algebraic Spaces, Tag 0BB6, first paragraph of the proof
(blueprint: lem-sfb-etale-affine-pairs-test-quasiseparated).

The fibre product is represented by a scheme whose underlying Zariski space is
quasi-compact. An isomorphism of presheaves specifies the representing scheme, so no
choice of a scheme representing the fibre product is built into the statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Absolute quasi-separatedness can be tested on pairs of affine representable étale charts.
Source: Stacks Project, Tag 0AHR, proof of (3) implies (1), restricted to affine opens of
an étale atlas; Tag 0BB6, first paragraph of the proof
(blueprint: lem-sfb-etale-affine-pairs-test-quasiseparated).

Proof:
1. Absolute quasi-separatedness applies to arbitrary affine scheme maps, hence to étale
ones [def-sfb-space-absolute-quasi-separated]. The representable diagonal
[def-trf-algebraic-space] represents their fibre product. For a scheme, its identity atlas
identifies its point topology with its Zariski topology
[lem-a1-space-affine-etale-cover], giving compactness of the representing scheme.
2. Conversely choose an atlas W = coproduct U_i with affine components
[lem-a1-space-affine-etale-cover]. Open inclusions are representable étale by base change
and étaleness of open immersions [lem-weil-pbc-open-immersion-base-change,
lem-weil-pbc-open-immersion-etale]. Composition and the scheme-source comparison
[lem-trf-space-chartwise-etale-permanence] make each U_i -> X representable étale.
The hypothesis makes each R_ij = U_i x_X U_j quasi-compact.
3. All products here are over Spec Z. The map W x W -> X x X is a composite of two
base changes of W -> X, hence surjective étale
[lem-trf-space-fibre-products-etale-covers, lem-trf-space-chartwise-etale-permanence].
Pulling back the representable diagonal gives j : R = W x_X W -> W x W.
4. The products Q_ij = U_i x U_j form an affine open covering of W x W
[lem-weil-pbc-open-immersion-base-change, def-pc-fibre-product,
lem-weil-pbc-fibre-product-affine-spectra]. Their inverse images under j are R_ij.
5. Each Q_ij is quasi-separated [lem-weil-pbc-affine-scheme-qcqs]; quasi-compactness of
R_ij therefore makes R_ij -> Q_ij quasi-compact [lem-weil-pbc-qcqs-morphism-permanence].
Locality on the target makes j quasi-compact [lem-pc-quasi-compact-local-on-target].
6. For a quasi-compact space Z -> W x W, choose a quasi-compact scheme atlas T -> Z.
Base change and composition [lem-weil-pbc-qcqs-morphism-permanence] make R x_(W x W) T
quasi-compact. It surjects étale onto R x_(W x W) Z by
[lem-trf-space-fibre-products-etale-covers], so j passes quasi-compact space tests.
Descend along W x W -> X x X [lem-sfb-space-quasicompact-fppf-local]; étale scheme tests
are flat and locally of finite presentation [def-weil-etale-morphism]. The representable
comparison [lem-sfb-space-quasicompact-affine-tests] gives quasi-compactness of every
scheme test of the absolute diagonal.
7. For arbitrary affine U,V -> X, their absolute product U x V is affine and
quasi-compact [lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-affine-scheme-qcqs].
The fibre product is X x_(X x X) (U x V) [def-pc-fibre-product], quasi-compact by step 6
and [lem-weil-pbc-qcqs-morphism-permanence]. Its point topology is its Zariski topology
by step 1, verifying the defining affine test [def-sfb-space-absolute-quasi-separated].
No finite atlas, quasi-compactness, separation, or Noetherian hypothesis on X is used. -/
theorem isAbsolutelyQuasiSeparated_iff_etale_affine_pairs
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    IsAbsolutelyQuasiSeparated X ↔
      ∀ (U V : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
        (a : yoneda.obj U ⟶ X.obj.obj) (b : yoneda.obj V ⟶ X.obj.obj),
        IsAffine U.left → IsAffine V.left → IsEtale a → IsEtale b →
          ∃ P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))),
            Nonempty (yoneda.obj P ≅ Limits.pullback a b) ∧ CompactSpace P.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
