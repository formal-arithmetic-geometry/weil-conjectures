/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Fibre products of quasi-compact quasi-separated algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 073B(3)
(blueprint: lem-sfb-qcqs-space-fibre-product).

Quasi-compactness uses the atlas topology on field-valued point classes. Absolute
quasi-separatedness uses the existing affine-pair test, without any condition on the base.
The fibre product is the sheaf pullback, bundled using its existing algebraicity theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A fibre product of quasi-compact and absolutely quasi-separated algebraic spaces is
quasi-compact and absolutely quasi-separated, over an arbitrary ambient scheme.
Source: Stacks Project, Morphisms of Spaces, Tag 073B(3)
(blueprint: lem-sfb-qcqs-space-fibre-product).

Proof:
1. Reconcile affine-scheme tests with quasi-compact-space tests. A quasi-compact point
   space admits an affine surjective étale atlas by [lem-sfb-qc-space-affine-etale-atlas].
   Conversely a quasi-compact scheme atlas has quasi-compact point space by
   [lem-a1-space-finite-affine-subatlas]. For a quasi-compact space test, choose such an
   affine atlas and pull it back by [lem-trf-space-fibre-products-etale-covers]. Its
   continuous surjective point map, supplied by [lem-a1-space-point-open-calculus],
   descends quasi-compactness by [lem-a1-space-finite-affine-subatlas]. This applies to
   diagonals too; affine tests give the converse immediately.
2. By [lem-sfb-space-qcqs-permanence], the map f is quasi-compact and quasi-separated,
   since A is qcqs and C is absolutely quasi-separated.
3. Put P = A ×_C B and p : P → B. For any affine T → B, the sheaf-pullback identity
   P ×_B T ≅ A ×_C T proves p quasi-compact. The relative diagonal of p is the base
   change of that of f: on sections, two pairs with the same B-coordinate agree exactly
   when their A-coordinates agree. Its affine tests are therefore quasi-compact, so p
   is quasi-separated. Algebraicity and the pullback identities use
   [lem-trf-space-fibre-products-etale-covers], rather than point-space pullbacks.
4. Test the quasi-compact map p against the identity of the quasi-compact space B.
   Step 1 gives quasi-compactness of P ×_B B ≅ P.
5. The source-over-quasi-separated-target assertion of [lem-sfb-space-qcqs-source-products]
   applied to p makes P absolutely quasi-separated, since B is absolutely quasi-separated.
   This uses the absolute convention over Spec Z and needs no separation property of S;
   the separate fibre-product assertion of that node is not used. -/
theorem qcqs_fibreProduct {S : Scheme.{u}} (A B C : AlgebraicSpace S)
    (f : A ⟶ C) (g : B ⟶ C)
    (hAqc : CompactSpace (Point A.obj.obj)) (hAqs : IsAbsolutelyQuasiSeparated A)
    (hBqc : CompactSpace (Point B.obj.obj)) (hBqs : IsAbsolutelyQuasiSeparated B)
    (hCqc : CompactSpace (Point C.obj.obj)) (hCqs : IsAbsolutelyQuasiSeparated C) :
    CompactSpace (Point (Limits.pullback f.hom g.hom).obj) ∧
      IsAbsolutelyQuasiSeparated
        (⟨Limits.pullback f.hom g.hom,
          (fibreProduct_isAlgebraicSpace A B C f g).1⟩ : AlgebraicSpace S) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
