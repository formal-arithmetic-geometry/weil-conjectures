/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage

/-! # Schematicity descends to a stage of an affine algebraic-space limit

Source: Stacks Project, Limits of Algebraic Spaces, Tag 07SR (lemma-limit-is-scheme),
under Situation 084R (situation-descent)
(blueprint: lem-sfb-affine-space-limit-schematic-stage).

Quasi-compactness uses the existing topology on field-valued point classes.
Quasi-separatedness is absolute, using the equivalent affine-pair criterion of Tag 0AHR.
The limit is taken in algebraic spaces over S, rather than assumed to be a sheaf limit.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a directed inverse limit of qcqs algebraic spaces with affine transition maps
is represented by a scheme, then some stage is represented by a scheme.

Source: Stacks Project, Limits of Algebraic Spaces, Tag 07SR, Situation 084R;
Properties of Spaces, Tags 03E4 and 0AHR
(blueprint: lem-sfb-affine-space-limit-schematic-stage).

Proof:
1. By the atlas criterion `points_compactSpace_iff` of lem-a1-space-etale-open-image,
   each stage admits a surjective etale chart from a quasi-compact scheme. The
   absolute quasi-separatedness hypothesis is precisely the diagonal condition of
   lem-sfb-space-affine-limits-schematic-stages, by the affine-pair criterion of
   Tag 0AHR. The affine scheme-test hypothesis gives its affine transition maps.
2. By lem-sfb-space-affine-limits-schematic-stages the limit L of the associated
   fppf sheaves is an algebraic space. Maps from any algebraic space W to L are
   exactly compatible families of maps from W to the stages, since a natural
   transformation into the sheaf limit is uniquely specified by its components.
   Thus L is also a limit in algebraic spaces over S. The universal property hc
   gives maps a : c.pt → L and b : L → c.pt commuting with all projections.
   Uniqueness in the two limit properties gives ba = id and ab = id.
3. Compose the scheme representation of c.pt with a to represent L by a scheme.
   Apply the schematic-stage clause of lem-sfb-space-affine-limits-schematic-stages.
   The index is small, directed and nonempty; step 1 supplies exactly its qcqs and
   affine hypotheses. It yields a stage represented by a scheme, as asserted. -/
theorem exists_scheme_stage_of_isLimit {S : Scheme.{u}}
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    (hqc : ∀ i : I, CompactSpace (Point (D.obj (op i)).obj.obj))
    (hqs : ∀ i : I, IsAbsolutelyQuasiSeparated (D.obj (op i)))
    (haff : ∀ (i j : Iᵒᵖ) (f : i ⟶ j),
      IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) (D.map f).hom.hom)
    (hscheme : ∃ U : Over S, Nonempty (yoneda.obj U ≅ c.pt.obj.obj)) :
    ∃ (i : I) (U : Over S), Nonempty (yoneda.obj U ≅ (D.obj (op i)).obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
