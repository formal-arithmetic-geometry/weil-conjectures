/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Finite affine refinement of an fppf covering

Source: Stacks Project, Topologies, Lemma 34.7.4 (Tag 021P)
(blueprint: lem-pc-fppf-affine-refinement).
-/

@[expose] public section

universe v u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An fppf covering of an affine scheme has a finite fppf refinement by affine opens of its
members. Source: Stacks Project, Topologies, Lemma 34.7.4 (Tag 021P)
(blueprint: lem-pc-fppf-affine-refinement).

Cover each member of the original family by affine opens. Their inclusions are open
immersions, so their composites with the original maps remain flat and locally of finite
presentation. These composites have open images and jointly cover the affine base. Its
quasi-compactness supplies a finite subcover. The selected affine opens, with their maps
factoring through the original members, form the required fppf covering. -/
theorem exists_finite_fppf_affine_open_refinement {U : Scheme.{u}} [IsAffine U]
    {I : Type v} (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ U)
    (hf : Presieve.ofArrows T f ∈ fppfPrecoverage U) :
    ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (T (i j)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
        Presieve.ofArrows (fun j ↦ (V j).toScheme)
          (fun j ↦ (V j).ι ≫ f (i j)) ∈ fppfPrecoverage U := by
  sorry

end AlgebraicGeometry.Scheme
