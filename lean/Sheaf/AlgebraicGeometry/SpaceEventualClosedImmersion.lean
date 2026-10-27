/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # A closed immersion into an algebraic-space limit is eventually closed

Source: Stacks Project, Limits of Algebraic Spaces, Tag 0828(1)
(blueprint: lem-sfb-space-eventual-closed-immersion).

The limit is explicitly taken in fppf sheaves. All arrows are over the algebraic
space B, and quasi-compactness is expressed by existence of a quasi-compact scheme
atlas. No quasi-separatedness or transition-surjectivity condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A closed immersion from a space locally of finite type over B into a directed
limit with quasi-compact stages and affine transitions is closed at every late stage.
Source: Stacks Project, Limits of Algebraic Spaces, Tag 0828(1)
(blueprint: lem-sfb-space-eventual-closed-immersion).

Proof:
1. Fix an initial index o. Refine an atlas of X_o to a finite affine atlas C by
   [lem-trf-space-qc-finite-affine-atlas-refinement]. Apply
   [lem-a1-qc-map-affine-etale-neighbourhood] to C to B to obtain an affine etale
   neighbourhood W of its image.
2. Form C times_B W and refine its atlas to an affine U_o covering X_o, using
   [lem-trf-space-qc-finite-affine-atlas-refinement]. The comparison U_o to
   X_o times_B W is etale by [lem-trf-space-representable-etale-scheme-tests].
3. Pull this chart back to X_i for i above o and to X. By
   [lem-sfb-space-affine-limits-schematic-stages] and [lem-sfb-space-affine-locality],
   all chart sources U_i and U are affine. The sheaf-limit universal property,
   [def-trf-algebraic-space], and Yoneda identify U with the scheme limit of U_i.
4. Put V = T times_X U. The closed-immersion affine-cover criterion
   [lem-weil-pbc-closed-immersion-affine-cover-criterion] makes V affine. It is etale
   over T times_B W, hence locally of finite type over W by the chart test and
   [lem-trf-space-representable-etale-scheme-tests]. Therefore its coordinate ring
   D is finitely generated over the coordinate ring R of W, by
   [lem-weil-pbc-lft-affine-pairs].
5. Write U_i = Spec A_i and U = Spec A. By [lem-weil-pbc-limit-affine-transition]
   and [lem-weil-pbc-limit-global-sections-colimit], A is the filtered colimit of
   the A_i. The closed immersion V to U gives a surjection A to D.
6. Choose finitely many R-algebra generators of D. Lift their preimages in A to a
   common stage A_j. Then A_j to D is surjective, as is A_i to D for every i above j.
7. The affine-cover criterion
   [lem-weil-pbc-closed-immersion-affine-cover-criterion] makes V to U_i closed
   for every i above j. Pullback associativity identifies this map with the base
   change of T to X_i along U_i to X_i.
8. The latter chart is representable surjective etale by
   [lem-trf-space-representable-etale-scheme-tests], and is flat and locally of
   finite presentation by [def-weil-etale-morphism]. Apply
   [lem-sfb-space-closed-immersion-fppf-descent] to conclude that T to X_i is a
   representable closed immersion for every i above j. -/
theorem eventually_isClosedImmersion_of_sheafLimit
    {S : Scheme.{u}} (B : AlgebraicSpace S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over B)
    (hqc : ∀ i : Iᵒᵖ, ∃ (U : Over S)
      (a : yoneda.obj U ⟶ (D.obj i).left.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (haff : ∀ {i j : Iᵒᵖ} (f : i ⟶ j),
      IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) (D.map f).left.hom.hom)
    (c : Cone D)
    (hc : IsLimit ((Over.forget B ⋙ ObjectProperty.ι (IsAlgebraicSpace (S := S))).mapCone c))
    (T : Over B) (h : T ⟶ c.pt)
    (hclosed : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) h.left.hom.hom)
    (hlft : MapIsLocally (@LocallyOfFiniteType) T.hom) :
    ∃ i₁ : I, ∀ i : I, i₁ ≤ i →
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (h.left ≫ (c.π.app (op i)).left).hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
