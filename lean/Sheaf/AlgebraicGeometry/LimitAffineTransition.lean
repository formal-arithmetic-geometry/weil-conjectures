/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Existence of inverse limits with affine transition morphisms

Source: Stacks Project, Limits, Lemmas 01YX and 01YW
(blueprint: lem-weil-pbc-limit-affine-transition).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An inverse system over a directed set with affine transition morphisms has a limit,
its projections are affine, and inverse images of arbitrary opens of any stage are limits
of the corresponding inverse images. For affine stages the limit is the spectrum of the
colimit of their global sections.

Source: Stacks Project, Limits, Lemmas 01YX and 01YW
(blueprint: lem-weil-pbc-limit-affine-transition).

Proof:
1. Choose a stage i₀. The upper tail is cofinal by directedness, so it suffices to construct
   the limit there (lem-weil-pbc-colimit-initial-full-subcategory).
2. For each i ≥ i₀, the affine morphism to Sᵢ₀ is the relative spectrum of the quasi-coherent
   algebra Aᵢ = fᵢᵢ₀,* Oᵢ. Transitions induce compatible algebra maps
   (lem-weil-pbc-affine-morphism-relative-spec).
3. Their colimit A is quasi-coherent, with sections on affine opens given by the colimit
   of sections (lem-weil-pbc-quasi-coherent-algebra-colimit).
4. Set S = Spec over Sᵢ₀ of A. The algebra coprojections give compatible scheme projections
   (lem-weil-pbc-affine-morphism-relative-spec).
5. Over each affine open of Sᵢ₀ the resulting cone is the spectrum of a colimit of rings,
   hence limiting (lem-weil-pbc-spec-colimit-limit).
6. Two maps to S with the same projections agree locally on inverse images of these
   affine opens, hence globally (lem-weil-pbc-scheme-morphism-gluing).
7. For any compatible cone from T, choose affine opens in T mapping into affine opens
   of Sᵢ₀. Step 5 supplies local factorizations, Step 6 makes them agree on intersections,
   and gluing gives the unique global factorization. Cofinality extends this to all stages
   (def-pc-scheme, lem-weil-pbc-scheme-morphism-gluing).
8. Every projection is affine, and restriction to any open of a stage is limiting with
   affine transitions (lem-weil-pbc-limit-cone-affine-projections-opens).
9. If every stage is affine, the spectrum of the colimit of their global sections is
   another limit cone (lem-weil-pbc-spec-colimit-limit). Uniqueness of limits gives the
   isomorphism compatible with every projection. -/
theorem exists_limit_affine_transition
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] :
    ∃ c : Cone D, Nonempty (IsLimit c) ∧
      (∀ i : Iᵒᵖ, IsAffineHom (c.π.app i)) ∧
      (∀ (i : Iᵒᵖ) (U : (D.obj i).Opens),
        Nonempty (IsLimit (opensCone D c i U)) ∧
          ∀ {j k : Over i} (f : j ⟶ k), IsAffineHom ((opensDiagram D i U).map f)) ∧
      ((∀ i : Iᵒᵖ, IsAffine (D.obj i)) →
        ∃ e : c.pt ≅ Spec (colimit (D.op ⋙ Scheme.Γ)),
          ∀ i : Iᵒᵖ, e.hom ≫ Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (op i)) =
            c.π.app i ≫ (ΓSpec.adjunction.unit.app (D.obj i))) := by
  sorry

end AlgebraicGeometry
