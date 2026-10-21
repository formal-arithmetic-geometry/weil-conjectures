/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf

/-!
# Natural linear comparison of equivariant coequalizers

Source: Stacks Project, Categories, Tag 002A, definition-coequalizers and the following
uniqueness paragraph; equivariant and natural refinement for the final clause of the
current blueprint's lem-sfb-extend-to-qlbar-constructible.proof.md.
(blueprint: lem-sfb-equivariant-coequalizer-comparison)
-/

@[expose] public section

universe uD vD uJ vJ

open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- Two natural, equivariant coequalizer presentations of internal modules have a unique
natural module isomorphism normalized by their quotient maps, and its inverse has the
opposite normalization. The tensor hypotheses concern only the displayed coforks.

Source: Stacks Project, Categories, Tag 002A, definition-coequalizers and the following
uniqueness paragraph; the equivariant and natural refinement is the direct argument in
this node, serving the final clause of lem-sfb-extend-to-qlbar-constructible.proof.md.
(blueprint: lem-sfb-equivariant-coequalizer-comparison)

Proof:
1. A coequalizer is epic: two maps agreeing after its projection are two factorizations
of the same equalizing map, so uniqueness identifies them. This applies to both quotient
maps and to both tensor images by the four assumed colimit universal properties.
2. At each j, factor q_j uniquely through r_j to obtain c_j, and factor r_j uniquely
through q_j to obtain d_j. This uses no module structure on H_j.
3. Precompose d_j c_j with r_j and c_j d_j with q_j. The normalization equations make
both composites identities after those projections; step 1 cancels the projections.
4. Precompose the action equation for c_j with A tensor r_j. Equivariance of r_j and
q_j, c_j r_j = q_j, and functoriality of tensor make both sides equal. Cancel A tensor
r_j by step 1. The module-morphism definition of sk-def-sfb-module-objects gives linearity.
5. Similarly, precompose the action equation for d_j with A tensor q_j, use equivariance
and d_j q_j = r_j, and cancel A tensor q_j to obtain linearity of d_j.
6. For u : j to k, precompose the naturality square for c with r_j. Naturality of q and
r and c_j r_j = q_j identify the composites; cancel r_j to get naturality in modules.
7. For d, precompose its naturality square with q_j, use naturality of r and q and
its normalization, and cancel q_j. Module morphisms have the underlying composition.
8. Assemble c and d into natural module transformations. Step 3 proves that they are
inverse. For any second normalized comparison, precompose each component with r_j and
cancel; componentwise equality gives equality of natural isomorphisms. Every step is
objectwise or arrowwise in J, so no colimit over J or smallness of J is used.
-/
theorem existsUnique_equivariant_coequalizer_comparison
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    (A : D) [MonObj A] {J : Type uJ} [Category.{vJ} J]
    (H : J ⥤ D) (B P Q : J ⥤ Mod D A)
    (a b : H ⟶ B ⋙ Mod.forget (D := D) A)
    (q : B ⋙ Mod.forget (D := D) A ⟶ P ⋙ Mod.forget (D := D) A)
    (r : B ⋙ Mod.forget (D := D) A ⟶ Q ⋙ Mod.forget (D := D) A)
    (hq : ∀ j : J, a.app j ≫ q.app j = b.app j ≫ q.app j)
    (hr : ∀ j : J, a.app j ≫ r.app j = b.app j ≫ r.app j)
    (hq_colimit : ∀ j : J, IsColimit (Cofork.ofπ (q.app j) (hq j)))
    (hr_colimit : ∀ j : J, IsColimit (Cofork.ofπ (r.app j) (hr j)))
    (hq_linear : ∀ j : J,
      IsModHom A (M := (B.obj j).X) (N := (P.obj j).X) (q.app j))
    (hr_linear : ∀ j : J,
      IsModHom A (M := (B.obj j).X) (N := (Q.obj j).X) (r.app j))
    (hq_tensor : ∀ j : J,
      IsColimit ((tensorLeft A).mapCocone (Cofork.ofπ (q.app j) (hq j))))
    (hr_tensor : ∀ j : J,
      IsColimit ((tensorLeft A).mapCocone (Cofork.ofπ (r.app j) (hr j)))) :
    ∃! c : Q ≅ P,
      (∀ j : J, r.app j ≫ (c.hom.app j).hom = q.app j) ∧
      (∀ j : J, q.app j ≫ (c.inv.app j).hom = r.app j) := by
  sorry

end CategoryTheory
