/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Category.Grp.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace

/-! # Separated group algebraic spaces over an algebraic closure

Source: Stacks Project, More on Groupoids in Spaces, Tag 0B8E,
`lemma-group-space-scheme-over-kbar`
(blueprint: lem-sfb-separated-group-space-geometric-scheme).

The group operations are encoded by a group-valued functor with underlying presheaf
isomorphic to the given algebraic space. Restriction along `Over.map` is its geometric
base change: a test scheme over the new field already specifies its second projection
to that field, so its sections are exactly the compatible pairs in the sheaf fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated group algebraic space becomes a scheme over any algebraic closure.
Source: Stacks Project, More on Groupoids in Spaces, Tag 0B8E
(blueprint: lem-sfb-separated-group-space-geometric-scheme).

Proof:
1. The closed diagonal is quasi-compact on affine scheme tests, since its inverse
   image is `Spec (A/I)`. Field base changes remain algebraic spaces by
   [lem-trf-space-fibre-products-etale-covers], with the induced group operations.
   The scheme-test calculation [lem-a1-space-monic-diagonal-tests], with the identity
   monomorphism, preserves the closed diagonal and its quasi-compactness.
2. Choose a surjective etale scheme atlas `U → G`. By
   [lem-sfb-scheme-large-algclosed-jacobson], choose a sufficiently large algebraically
   closed extension `K/k` such that `U_K` is Jacobson with all closed points K-rational.
   Its base change is still a surjective etale atlas of `H = G_K`.
3. The largest schematic open `W` exists by [lem-sfb-space-dense-schematic-locus].
   It contains the dense scheme open of [lem-sfb-quasiseparated-space-dense-scheme-open]
   by maximality. The identity makes `H` nonempty, so its inverse image in `U_K` is a
   nonempty open, by [lem-a1-space-etale-open-image]. It contains a closed point,
   whose residue field is `K`; hence `W` has a K-rational point `g'`.
4. Every automorphism preserves `W`: maximality gives inclusion, and the inverse
   gives the reverse inclusion. Translation `h ↦ g (g')⁻¹ h` is an automorphism
   taking `g'` to any prescribed K-point `g`, by the group laws. Thus all K-points
   lie in `W`, using [def-a1-space-open-subspace].
5. The complement of the inverse image of `W` in `U_K` is closed and contains no
   closed point. Its closed points are dense by the Jacobson property of Step 2,
   so it is empty. Surjectivity of the atlas and the open-subspace correspondence
   of [lem-a1-space-etale-open-image] imply `W = H`; thus `G_K` is a scheme.
6. Apply [lem-sfb-space-scheme-after-field-extension] to `G` and `K/k`, using the
   quasi-separatedness of Step 1, to conclude that its algebraic-closure base change
   is a scheme. No finite-type, reducedness, smoothness or commutativity is used. -/
theorem exists_scheme_over_algebraicClosure_of_separated
    {k : Type u} [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (G : AlgebraicSpace (Spec (.of k)))
    (F : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (e : F ⋙ forget GrpCat ≅ G.obj.obj)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 G.obj.obj) (𝟙 G.obj.obj))) :
    ∃ X : Over (Spec (.of Ω)),
      Nonempty
        (((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).op ⋙ G.obj.obj) ≅
          yoneda.obj X) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
