/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology

/-! # Properness cancellation for algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 04NX(2)
(blueprint: lem-sfb-space-proper-cancellation).

The existing morphism properties apply to arbitrary algebraic spaces. Quasi-compactness
is tested after every affine scheme base change, whose compact point space equivalently
admits a surjective etale atlas from a quasi-compact scheme (Stacks, Tag 03E4).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a composite of algebraic-space morphisms is proper and its second factor is
separated, its first factor is proper. No representability or finiteness-presentation
hypothesis is imposed.
Source: Stacks Project, Morphisms of Spaces, Tag 04NX(2)
(blueprint: lem-sfb-space-proper-cancellation).

Proof:
1. Set h = v o u and P = X times_Z Y. The sheaf fibre-product universal property
   [lem-trf-space-fibre-products-etale-covers] gives the graph gamma = (id_X, u)
   and identifies it as the pullback of Delta_v along (u o p_X, p_Y). On scheme
   tests, the compatible triples satisfy u(x) = y_0 = y, so are uniquely x.
   The composite of gamma with p_Y is u.
2. Separatedness of v makes Delta_v representable by closed immersions. Its scheme
   tests after the preceding pullback are still closed immersions, so gamma is a
   representable closed immersion. This assumes no representability of u or v.
3. By [lem-sfb-space-closed-subspace-proper], gamma is proper. By
   [lem-sfb-space-proper-base-change], p_Y is proper, being the base change of h.
4. To verify quasi-compactness in the affine-test sense, fix an affine W mapping to Y.
   The pullback P_W identifies with X times_Z W, and X_W with X times_P P_W.
   Quasi-compactness of h supplies a surjective etale quasi-compact scheme atlas U
   of P_W. Pulling it back to X_W gives a surjective etale scheme atlas U' by
   [lem-trf-space-fibre-products-etale-covers]. Because gamma is a representable
   closed immersion, U' is a closed subscheme of U, hence quasi-compact by
   [def-weil-pbc-quasi-compact-scheme]. Thus u is quasi-compact on affine tests.
5. Local finite type composes by [lem-sfb-stack-finite-type-calculus], whose space
   specialization agrees with etale scheme charts. Separatedness composes by
   [lem-sfb-space-separated-fp-composition]. Hence u is separated and of finite type.
6. After any algebraic-space base change to Y, u still factors through the two
   base-changed factors gamma and p_Y. Both point maps are closed by step 3.
   Applying maps to field-valued representatives shows the point map of their
   composite is their composite point map [def-a1-space-point-topology]. This is
   closed. Thus u is universally closed, and therefore proper. All tests remain
   over S. -/
theorem mapIsProper_of_comp_of_mapIsSeparated {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (u : X ⟶ Y) (v : Y ⟶ Z)
    (hproper : MapIsProper (u ≫ v)) (hsep : MapIsSeparated v) : MapIsProper u := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
