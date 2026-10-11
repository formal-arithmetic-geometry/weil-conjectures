/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-!
# Descent of constructible module sheaves along inverse limits

Source: Stacks Project, Etale Cohomology, Lemma 59.73.10, Tag 09YU (3),
essential surjectivity for finite commutative coefficients
(blueprint: lem-weil-pbc-constructible-module-limit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A constructible etale sheaf of modules over a finite commutative ring on the limit
of a directed inverse system of qcqs schemes with affine transitions descends to a
constructible module sheaf at one stage, up to module-sheaf isomorphism.

Source: Stacks Project, Tag 09YU (3), essential surjectivity
(blueprint: lem-weil-pbc-constructible-module-limit-descent).

Proof (the module argument expands the source's instruction to use Tag 095N):
1. The limit is qcqs: its projections are affine by
   `lem-weil-pbc-limit-affine-transition`, and affine morphisms preserve qcqs over a
   qcqs base (`lem-weil-pbc-affine-morphism-permanence`,
   `lem-weil-pbc-qcqs-morphism-permanence`). The free Yoneda module on an etale object W,
   after sheafification, represents sections over W
   (`lem-weil-pbc-free-yoneda-presheaf-module`, `def-weil-presheaf-modules-sheafification`).
2. Present F as the cokernel of a map between finite sums of these free modules on
   affine etale objects (`lem-weil-pbc-constructible-module-finite-presentation`).
   A map from such a sum is determined by its generating sections.
3. Descend the finitely many affine etale objects to a common stage by directedness
   (`lem-weil-pbc-affine-etale-site-colimit`), using compatibility of base change.
4. Inverse image carries the descended free modules to the original ones, compatibly
   with their generating sections (`lem-weil-pbc-inverse-image-free-etale-module`), and
   preserves their finite sums (`prop-weil-pbc-inverse-image-modules-exact`).
5. Descend the finitely many generating sections of the presentation map to a common
   later stage (`lem-weil-pbc-limit-pullback-sections-colimit`).
6. Use these sections to define a presentation map there. After inverse image it is
   the original map: check each generator, using the free-module compatibility from
   step 4, the section comparison from step 5 and inverse-image composition
   (`lem-weil-pbc-inverse-image-composition`, `lem-weil-pbc-inverse-image-module-adjunction`).
7. Take the cokernel at that stage. It is constructible: the free summands are
   constructible (`lem-weil-pbc-etale-free-sheaf-constructible`), inverse image preserves
   constructibility (`prop-constructible-pullback`), and constructible module sheaves
   are closed under finite sums and cokernels (`thm-constructible-serre`).
8. Inverse image preserves cokernels (`prop-weil-pbc-inverse-image-modules-exact`), so
   the commuting presentation square identifies its cokernel with F. -/
theorem exists_constructible_etaleModuleSheaf_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    ∃ (i : I) (Fᵢ : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsConstructibleEtaleModuleSheaf Fᵢ ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj Fᵢ ≅ F) := by
  sorry

end AlgebraicGeometry.Scheme
