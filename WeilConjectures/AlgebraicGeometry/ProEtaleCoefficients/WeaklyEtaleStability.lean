/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale

/-!
# Stability of weakly étale and affine pro-étale morphisms

Source: blueprint node `sk-lem-pe-weakly-etale-stability`, order 702, and Stacks
Project, Tag 092A (blueprint: sk-lem-pe-weakly-etale-stability).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

/-- Weakly étale morphisms are stable under base change and composition, are Zariski-local on
source and target, and satisfy the over-base morphism property. Affine pro-étale morphisms are
stable under affine base change and composition.

Source: blueprint node `sk-lem-pe-weakly-etale-stability`, order 702, proof steps 1--5,
and Stacks Project, Tag 092A (blueprint: sk-lem-pe-weakly-etale-stability).

Proof: Mathlib's weakly etale instances give base-change stability, composition,
and Zariski locality on source and target. For a morphism over a base, rewrite the
weak etaleness of its structure map using the commuting triangle, then apply
`WeaklyEtale.of_comp`. The source library's pro-affine etale composition and affine
base-change instances give the final two clauses. These instances already implement
the diagonal and ind-etale arguments of the blueprint, so no additional ring stability
or principal ind-Zariski results are needed here.
-/
theorem weaklyEtale_stability :
    MorphismProperty.IsStableUnderBaseChange @WeaklyEtale.{u} ∧
      MorphismProperty.IsStableUnderComposition @WeaklyEtale.{u} ∧
      IsZariskiLocalAtSource @WeaklyEtale.{u} ∧
      IsZariskiLocalAtTarget @WeaklyEtale.{u} ∧
      (∀ {S U V : Scheme.{u}} (u : U ⟶ S) (v : V ⟶ S) (f : U ⟶ V),
        WeaklyEtale u → WeaklyEtale v → f ≫ v = u → WeaklyEtale f) ∧
      (∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
        (f : X ⟶ Y) (g : Y ⟶ Z),
        proAffineEtale f → proAffineEtale g → proAffineEtale (f ≫ g)) ∧
      (∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y),
        proAffineEtale.{u}.IsStableUnderBaseChangeAlong f) := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro S U V u v f hu hv h
    have : WeaklyEtale (f ≫ v) := h.symm ▸ hu
    exact WeaklyEtale.of_comp f v
  · intro X Y Z _ _ _ f g hf hg
    exact proAffineEtale.comp_mem f g hf hg
  · intro X Y _ _ f
    infer_instance

end AlgebraicGeometry
