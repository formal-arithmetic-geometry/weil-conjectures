/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue fields at points of inverse limits

Source: Stacks Project, Limits, Lemma 0CUG (1)
(blueprint: lem-weil-pbc-limit-residue-field).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The residue field at a point of an inverse limit with affine transitions is the
colimit of the residue fields of its images. The spectra form a limiting cone, compatible
with the canonical maps into the original schemes. `HEq` identifies the actual canonical
maps despite the equal, but not definitionally equal, image points in their source types.
No arbitrary transition or projection maps are allowed by these identifications.

Source: Stacks Project, Limits, Lemma 0CUG (1)
(blueprint: lem-weil-pbc-limit-residue-field).

Proof:
1. The cone identities identify the image of s_j under each transition with s_i.
   Functoriality of stalk and residue maps gives the residue-field diagram and cocone
   (def-weil-residue-field, def-weil-pbc-category-colimit).
2. Choose a stage i₀. Its upper tail is cofinal, so a colimit on that tail suffices
   (lem-weil-pbc-colimit-initial-full-subcategory).
3. Choose an affine neighbourhood of s_i₀ and pull it back to every later stage and
   to the limit. These schemes are affine and still form a limit; their residue fields
   identify with the original ones through the open immersions
   (lem-weil-pbc-limit-affine-transition, lem-weil-pbc-residue-field-point-naturality).
4. Write the affine system as Spec A_i and its limit as Spec A, where A is the colimit
   of A_i. The image primes are the preimages of the prime of s, and the scheme residue
   maps are the induced algebraic residue maps
   (lem-weil-pbc-limit-global-sections-colimit,
   lem-weil-pbc-spec-map-residue-field-naturality).
5. Localization at the prime commutes with this filtered colimit. Every element of the
   localized ring, and hence its residue field, comes from a stage. All maps between
   these fields are injective
   (lem-weil-pbc-filtered-colimit-localization-at-prime,
   lem-weil-pbc-filtered-colimit-algebras-elementwise).
6. For any compatible family of ring maps out of the stage fields, define a map out of
   the limit field by choosing a stage representative. A common later stage and
   injectivity show independence of the representative. Common stages also prove the
   ring laws; coverage by stage images proves uniqueness (def-weil-pbc-category-colimit).
7. Taking spectra turns the ring colimit into a scheme limit
   (lem-weil-pbc-spec-colimit-limit). Naturality of the canonical residue-field point
   maps gives compatibility on every transition and projection
   (lem-weil-pbc-residue-field-point-naturality). -/
theorem exists_isColimit_residueField_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (s : c.pt) :
    ∃ (R : I ⥤ CommRingCat.{u}) (r : Cocone R),
      (∀ i : I, R.obj i = (D.obj (op i)).residueField (c.π.app (op i) s)) ∧
      (∀ (i j : I) (f : i ⟶ j),
        HEq (R.map f) ((D.map f.op).residueFieldMap (c.π.app (op j) s))) ∧
      r.pt = c.pt.residueField s ∧
      (∀ i : I, HEq (r.ι.app i) ((c.π.app (op i)).residueFieldMap s)) ∧
      Nonempty (IsColimit r) ∧
      (∃ t : Cone (R.op ⋙ Scheme.Spec),
        t.pt = Spec (c.pt.residueField s) ∧
        (∀ i : I, HEq (t.π.app (op i))
          (Spec.map ((c.π.app (op i)).residueFieldMap s))) ∧
        Nonempty (IsLimit t) ∧
        ∀ {i j : Iᵒᵖ} (f : i ⟶ j),
          IsAffineHom ((R.op ⋙ Scheme.Spec).map f)) ∧
      (∀ i : I, Spec.map ((c.π.app (op i)).residueFieldMap s) ≫
        (D.obj (op i)).fromSpecResidueField (c.π.app (op i) s) =
          c.pt.fromSpecResidueField s ≫ c.π.app (op i)) ∧
      (∀ (i j : I) (f : i ⟶ j),
        Spec.map ((D.map f.op).residueFieldMap (c.π.app (op j) s)) ≫
          (D.obj (op i)).fromSpecResidueField (D.map f.op (c.π.app (op j) s)) =
        (D.obj (op j)).fromSpecResidueField (c.π.app (op j) s) ≫ D.map f.op) := by
  sorry

end AlgebraicGeometry
