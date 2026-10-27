/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits

/-! # Finite finitely presented approximation of integral algebraic spaces

Source: Stacks Project, Limits of Spaces, Tag 09YA,
`lemma-integral-limit-finite-and-finite-presentation`
(blueprint: lem-sfb-integral-space-finite-presentation-limit).

Absolute quasi-separatedness is expressed by the affine-pair test from Properties of
Spaces, `lemma-characterize-quasi-separated`: for arbitrary affine schemes mapping to
`X`, their fibre product over `X` is quasi-compact. This does not assume anything about
the absolute diagonal of the base scheme `S`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An integral algebraic-space morphism with qcqs target is a directed inverse limit
of finite finitely presented morphisms, with affine transitions and qcqs stages.
Source: Stacks Project, Limits of Spaces, Tag 09YA,
`lemma-integral-limit-finite-and-finite-presentation`, including its relative-Spec
construction; Properties of Spaces, `lemma-characterize-quasi-separated` for the
absolute affine-pair test (blueprint: lem-sfb-integral-space-finite-presentation-limit).

Proof:
1. Integrality on scheme tests implies affineness. By
   [lem-sfb-space-relative-spec-correspondence], write Y as relative Spec of the
   integral quasi-coherent algebra A = p_* O_Y. Apply
   [lem-sfb-space-integral-algebra-fp-colimit] over the qcqs base X to express A as a
   small nonempty directed colimit of finite finitely presented algebras A_i. The
   colimit maps need not be inclusions.
2. Set Y_i = Spec_X A_i. The relative-Spec correspondence gives the finite finitely
   presented structure maps, the transitions, the projections, and their compatibility.
   By [lem-sfb-space-affine-locality] the stages are qcqs, using the equivalence of
   atlas and point-topological quasi-compactness in [lem-a1-space-etale-open-image].
   Choose an affine surjective etale atlas of X by
   [lem-sfb-qc-space-affine-etale-atlas]. Its pullbacks V_i are affine schemes; the
   base change of a transition is V_j to V_i by
   [lem-trf-space-fibre-products-etale-covers]. The target is separated by
   [lem-weil-pbc-affine-morphism-permanence], so this map is affine by
   [lem-weil-pbc-affine-source-separated-target-affine-morphism]. Descend affineness
   using [lem-sfb-space-affine-locality].
3. By [lem-sfb-space-affine-limits-schematic-stages] the system has an algebraic-space
   limit L over S with affine projections. Choose one index to define L to X;
   directedness and cone compatibility show every projection is over X. The universal
   map for any cone over X is over X, as checked after that chosen projection.
4. The algebra colimit and relative-Spec anti-equivalence show that Y is the limit in
   spaces affine over X, as is L. Uniqueness of limit maps makes the canonical maps
   between Y and L inverse. Transport the limit property of L to Y. This is a limit
   in the whole category over X, so its test objects are all algebraic spaces W/X. -/
theorem exists_finite_finitePresentation_limit_of_integral
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (p : Y ⟶ X)
    (hp : IsRepresentableWith (fun _ _ f ↦ IsIntegralHom f.left) p.hom.hom)
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b))) :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Over X)
      (π : (Functor.const Iᵒᵖ).obj (Over.mk p) ⟶ D),
      (∀ i : Iᵒᵖ,
        IsRepresentableWith (fun _ _ f ↦ IsFinite f.left) (D.obj i).hom.hom.hom ∧
        MapIsQuasiCompact (D.obj i).hom.hom.hom ∧
        MapIsQuasiCompact (pullback.diagonal (D.obj i).hom.hom.hom) ∧
        MapIsLocallyOfFinitePresentation (D.obj i).hom ∧
        CompactSpace (Point (D.obj i).left.obj.obj) ∧
        ∀ (U V : Over S) (a : yoneda.obj U ⟶ (D.obj i).left.obj.obj)
          (b : yoneda.obj V ⟶ (D.obj i).left.obj.obj),
          IsAffine U.left → IsAffine V.left → CompactSpace (Point (Limits.pullback a b))) ∧
      (∀ (i j : Iᵒᵖ) (f : i ⟶ j),
        IsRepresentableWith (fun _ _ g ↦ IsAffineHom g.left) (D.map f).left.hom.hom) ∧
      Nonempty (IsLimit (Cone.mk (Over.mk p) π)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
