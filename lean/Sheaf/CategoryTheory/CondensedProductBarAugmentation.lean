/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.CategoryTheory.CondensedProductBarComparison
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
import Sheaf.CategoryTheory.CondensedInjectiveBarRows
import Sheaf.CategoryTheory.CondensedBarTotalAugmentation

/-! # The actual invariant augmentation of a product diagonal

Source: latest blueprint direct-image stability, paragraph (3), formal internal-bar
expansion, step 6 of the product resolution model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open Profinite.CondensedAction
namespace CategoryTheory.CondensedBar

variable {A : Ring.{u}} {G H : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The invariant inclusion into group degree zero of the diagonal total is a
quasi-isomorphism on any equivariant injective resolution.

Source: latest blueprint direct-image stability, paragraph (3), formal internal-bar
expansion, product-resolution-model step 6; Stacks Tags 0133 and 012X
(blueprint: lem-sfb-condensed-product-bar-augmentation).

Proof:
1. Reorder the parameter tuples G^n times H^n into (G times H)^n in each term of B.
The two first diagonal faces act by (g,1)(1,h)=(g,h); interior faces multiply the two
coordinates, final faces omit them, and degeneracies insert (1,1). Thus the diagonal
is the full inhomogeneous product-group bar, including its augmentation.
2. Apply the injective-row theorem to each injective term I^q, with group G times H.
The homogeneous-to-inhomogeneous coordinate map identifies the augmented row with
equivariant Hom from the free homogeneous bar into I^q. The free bar is exact;
injectivity extends maps across images, proving augmented-row exactness. Its
augmentation is exactly V.inclusion followed by B.augmentation, by normalization
on all generalized generators.
3. Equivariant resolution differentials commute with the invariant inclusions and
all bar operators. Therefore these inclusions define a chain map into the finite
first-quadrant total, supported in bar degree zero. The vertical sign there is +1.
4. The first-quadrant column-augmentation comparison, equivalently the total
augmentation theorem, applies to the exact augmented rows from step 2. It proves
that this very chain map is a quasi-isomorphism. The components are the displayed
invariant inclusion followed by the actual degree-zero total coprojection.
The proof uses only nonnegative finite diagonals and works for any chosen resolution
of zero; trivial factors retain all degrees of their unnormalized nerves.
-/
theorem exists_productBarAugmentation (B : ProductBar A.toMon G H)
    (V : Invariants A (G × H)) {N : Equivariant A (G × H)} (I : InjectiveResolution N) :
    ∃ j : (V.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
        B.diagonalTotal I.cocomplex,
      (∀ q : ℕ, j.f q =
        V.inclusion.app (I.cocomplex.X q) ≫ B.augmentation.app (I.cocomplex.X q) ≫
          B.diagonalZero I.cocomplex q) ∧ QuasiIso j := by sorry

end CategoryTheory.CondensedBar
