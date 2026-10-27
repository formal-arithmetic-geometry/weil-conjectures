/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover

/-! # Finite finitely presented approximation of finite space morphisms

Source: Stacks Project, Limits of Spaces, Tag 07VR,
`lemma-finite-in-finite-and-finite-presentation`
(blueprint: lem-sfb-space-finite-fp-approximation).

The affine-pair criterion in Properties of Spaces, `lemma-characterize-quasi-separated`,
expresses absolute quasi-separatedness without a separation assumption on the base scheme.
The diagram and its cone live in the category of algebraic spaces over the given target.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite map with qcqs target is a directed inverse limit of finite finitely presented
maps, with closed immersion transitions, which are also affine.
Source: Stacks Project, Limits of Spaces, Tag 07VR,
`lemma-finite-in-finite-and-finite-presentation`; Properties of Spaces,
`lemma-characterize-quasi-separated` for the absolute affine-pair criterion
(blueprint: lem-sfb-space-finite-fp-approximation).

Proof:
1. Finiteness on scheme tests implies affineness. By
   [lem-sfb-space-relative-spec-correspondence], identify X with the relative Spec of
   A = f_* O_X, a finite quasi-coherent algebra on Y. Apply
   [lem-sfb-space-finite-algebra-surjective-fp-colimit] to obtain a small nonempty
   directed colimit of finite finitely presented algebras A_i, with surjective transitions.
2. Set X_i = Spec_Y A_i. Contravariance and functoriality of relative Spec give the
   transitions, the projections from X, and all equations over Y. Its property tests give
   finiteness and finite presentation of X_i over Y; this is algebra finite presentation.
3. Choose affine etale charts U_lambda over Y by [lem-a1-space-affine-etale-cover].
   Their pullbacks V_i,lambda cover X_i by [lem-trf-space-fibre-products-etale-covers].
   A transition over V_i,lambda is Spec of the surjection on algebra sections.
   The affine characterization [def-weil-closed-immersion] makes it a closed immersion.
   By [lem-sfb-space-closed-immersion-atlas-locality], the transition is representable
   and a closed immersion on every scheme test, and hence affine there.
4. By [lem-sfb-space-affine-limits-schematic-stages], the sheaf limit L is an algebraic
   space with affine projections. Choose an index to define L to Y; directedness shows
   every projection has that composite to Y. The universal map from any cone over Y is
   over Y, as checked using that index. By [lem-sfb-space-affine-locality], L to Y is
   affine. The algebra colimit and relative-Spec anti-equivalence identify X as the limit
   in the full subcategory of spaces affine over Y, as is L. The unique cone maps X to L
   and L to X are inverse by uniqueness. Thus X, with the specified projections, is a
   limit among all spaces over Y. Each projection is a Y-map, giving the factorization. -/
theorem exists_finite_finitePresentation_limit_of_finite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : IsRepresentableWith (fun _ _ g ↦ IsFinite g.left) f.hom.hom)
    (hqc : CompactSpace (Point Y.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ Y.obj.obj)
      (b : yoneda.obj V ⟶ Y.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b))) :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Over Y)
      (π : (Functor.const Iᵒᵖ).obj (Over.mk f) ⟶ D),
      (∀ i : Iᵒᵖ,
        IsRepresentableWith (fun _ _ g ↦ IsFinite g.left) (D.obj i).hom.hom.hom ∧
        MapIsLocallyOfFinitePresentation (D.obj i).hom ∧
        MapIsQuasiCompact (D.obj i).hom.hom.hom ∧
        MapIsQuasiCompact (pullback.diagonal (D.obj i).hom.hom.hom)) ∧
      (∀ (i j : Iᵒᵖ) (a : i ⟶ j),
        IsRepresentableWith (fun _ _ g ↦ IsClosedImmersion g.left)
          (D.map a).left.hom.hom ∧
        IsRepresentableWith (fun _ _ g ↦ IsAffineHom g.left) (D.map a).left.hom.hom) ∧
      Nonempty (IsLimit (Cone.mk (Over.mk f) π)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
