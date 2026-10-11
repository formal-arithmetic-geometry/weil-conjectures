/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Affine refinement of a singleton fpqc covering

Source: Stacks Project, Topologies, Definition 022B and Lemma 022E, with the finite
coproduct construction (blueprint: lem-galois-fpqc-singleton-affine-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- If a singleton fpqc covering has affine base, finitely many affine opens of its source
give an affine coproduct whose induced map is flat, surjective, and an fpqc covering.

Source: Stacks Project, Topologies, Definition 022B and Lemma 022E
(blueprint: lem-galois-fpqc-singleton-affine-refinement).

Apply the finite affine-open image condition of the fpqc covering to the whole affine base;
the source map is flat. Form the finite coproduct of the chosen opens and use its universal
property to obtain the map to the original source. A finite coproduct of affine schemes is
affine. The induced map is surjective since the images of the opens cover the base, and it
is flat because the coprojections and the open inclusions identify the local rings with
those of the original flat map. Finally, for every affine open of the base, its inverse
image under the resulting flat surjection is affine and witnesses the singleton fpqc
condition. The empty family is allowed when the base is empty. -/
theorem exists_fpqc_singleton_affine_refinement {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (hf : Presieve.singleton f ∈ fpqcPrecoverage S) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ j, IsAffineOpen (U j)) ∧
      (let X' := ∐ (fun j : Fin n ↦ (U j).toScheme);
       ∃ (h : X' ⟶ X) (g : X' ⟶ S),
        (∀ j, Sigma.ι (fun k ↦ (U k).toScheme) j ≫ h = (U j).ι) ∧
        g = h ≫ f ∧ IsAffine X' ∧ Flat g ∧ Surjective g ∧
          Presieve.singleton g ∈ fpqcPrecoverage S) := by
  sorry

end AlgebraicGeometry.Scheme
