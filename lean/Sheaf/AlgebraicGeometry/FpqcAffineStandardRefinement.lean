/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Finite standard affine refinements of fpqc coverings

Source: Stacks Project, Topologies, Definition 022B, and Descent, Lemma 03N0
(blueprint: lem-weil-pbc-fpqc-affine-standard-refinement).
-/

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An fpqc covering of `Spec R` admits finitely many affine opens of its members such
that the induced map from `R` to the product of their coordinate rings is faithfully flat.
Source: Stacks Project, Definition 022B and Lemma 03N0
(blueprint: lem-weil-pbc-fpqc-affine-standard-refinement).

Proof:
1. Apply the affine-open condition of `def-weil-pbc-fpqc-covering` to the whole base.
   Select finitely many affine opens whose images cover it, allowing the empty family
   when the base is empty. Quasi-compact opens in Mathlib's formulation can be covered
   by finitely many affine opens.
2. Each coordinate map is flat by `lem-weil-pbc-flat-morphism-affine-criterion`
   (Stacks 01U5). Their finite product is flat by
   `lem-weil-pbc-finite-product-flat-modules`.
3. Every prime of `R` lifts to one selected coordinate ring because the images cover
   the base. Pull that prime back along the coordinate projection from the product.
   Thus the product map is surjective on spectra and is faithfully flat by
   `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat` (Stacks 00HQ).
The coordinate ring of an affine open is the global-section ring of its open subscheme;
its spectrum is canonically isomorphic to that subscheme. -/
theorem exists_fpqc_affine_standard_refinement (R : CommRingCat.{u})
    {I : Type v} (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ Spec R)
    (hf : Presieve.ofArrows T f ∈ fpqcPrecoverage (Spec R)) :
    ∃ (n : ℕ) (a : Fin n → I) (V : ∀ j, (T (a j)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
      (RingHom.pi (fun j : Fin n ↦
        ((ΓSpecIso R).inv ≫ ((V j).ι ≫ f (a j)).appTop).hom)).FaithfullyFlat := by
  sorry

end AlgebraicGeometry.Scheme
