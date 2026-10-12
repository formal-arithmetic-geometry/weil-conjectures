/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Closed subschemes of affine-transition limits -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The scheme-theoretic images of a closed subscheme in the stages form an
inverse system with affine transitions and with the original closed subscheme as limit.
Source: Stacks Project, Limits, Tag 0A0P (approximation argument), and
Morphisms, Tag 01R8 (quasi-compact scheme-theoretic images). The closed-image
implementation below is an argument written here, rather than the proof of 0A0P.
(blueprint: lem-weil-pbc-closed-image-limit-system)
Proof: define Z at j as the scheme-theoretic image of i followed by the j-th cone
leg. These maps are quasi-compact: affine-transition limit projections are affine,
and i is a closed immersion. Their image ideals are the kernels on affine opens.
Naturality of the cone puts the transition composite in the next image, so the
universal property of the image gives unique transition maps. Uniqueness proves
identity, composition, and naturality of the image inclusions and cone legs.
For an arrow j to k, the map Z_j to the inverse image of Z_k in D_j is a closed
immersion: its composite into D_j is the image inclusion, a closed immersion.
The inverse image projects affinely to Z_k since D_j to D_k is affine. Thus the
transition on images is affine. To check the limit, work over an affine open of
one stage and restrict to its cofinal over category. Write the coordinate rings
of the stages as B_j and of the closed subscheme as B/I, where B is their filtered
colimit. The image rings are B_j/ker(B_j to B/I). Their colimit is B/I: every
class lifts at some stage, and a class mapping to zero is already zero in the
corresponding quotient. Spectra turn this colimit into a limit of affine schemes.
These local identifications agree on overlaps because the image factorizations
are unique, and glue to the asserted limit cone with vertex X. -/
theorem exists_closed_image_limit_system
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u})
    [∀ {j k : J} (a : j ⟶ k), IsAffineHom (D.map a)]
    [∀ j : J, CompactSpace (D.obj j)]
    [∀ j : J, QuasiSeparatedSpace (D.obj j)]
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (πY : (Functor.const J).obj Y ⟶ D) (hY : IsLimit (Cone.mk Y πY)) :
    ∃ (Z : J ⥤ Scheme.{u}) (k : Z ⟶ D)
      (πX : (Functor.const J).obj X ⟶ Z),
      Nonempty (IsLimit (Cone.mk X πX)) ∧
      (∀ {j k : J} (a : j ⟶ k), IsAffineHom (Z.map a)) ∧
      (∀ j : J, IsClosedImmersion (k.app j)) ∧
      (∀ j : J, πX.app j ≫ k.app j = i ≫ πY.app j) := by sorry

end AlgebraicGeometry
