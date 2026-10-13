/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Rank on a clopen restriction and its change of base

Source: Mathlib Scheme.Hom.finrank_of_isPullback and isPullback_morphismRestrict;
corrected finite-étale lifting steps 3 and 5.
(blueprint: lem-weil-pbc-finite-etale-clopen-restriction-rank)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- A clopen restriction is finite étale, and its rank commutes with base change.
Source: corrected blueprint finite-étale lifting, steps 3 and 5; Stacks Tag 02KA.
(blueprint: lem-weil-pbc-finite-etale-clopen-restriction-rank)

Proof: The inclusion of a clopen open subscheme is both an open and a closed
immersion. Thus it is étale and finite; composing with q preserves both properties.
The same holds for its inverse image along j. Restrict the given cartesian square to
W and its inverse image: the resulting square is cartesian, since factorization
through an open subscheme is equivalent to image containment. Apply invariance of
the rank of a finite flat morphism in a cartesian square (Mathlib's
Scheme.Hom.finrank_of_isPullback) to this restricted square. No nonemptiness or
surjectivity of i is used. -/
theorem Scheme.finiteEtale_clopen_restriction_rank
    {X X₀ S S₀ : Scheme.{u}} (q : X ⟶ S) [IsFinite q] [Etale q]
    (j : X₀ ⟶ X) (q₀ : X₀ ⟶ S₀) (i : S₀ ⟶ S) (h : IsPullback j q₀ q i)
    (W : X.Opens) (hW : IsClosed (W : Set X)) :
    IsFinite (W.ι ≫ q) ∧ Etale (W.ι ≫ q) ∧
      IsFinite ((j ⁻¹ᵁ W).ι ≫ q₀) ∧ Etale ((j ⁻¹ᵁ W).ι ≫ q₀) ∧
      ∀ x : S₀, (((j ⁻¹ᵁ W).ι ≫ q₀).finrank x) = (W.ι ≫ q).finrank (i x)  := by
  have : IsClosedImmersion W.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hW)
  have : IsFinite q₀ := MorphismProperty.of_isPullback h inferInstance
  have : Etale q₀ := MorphismProperty.of_isPullback h inferInstance
  have hW₀ : IsClosed ((j ⁻¹ᵁ W) : Set X₀) := hW.preimage j.continuous
  have : IsClosedImmersion (j ⁻¹ᵁ W).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hW₀)
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro x
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _
    ((isPullback_morphismRestrict j W).paste_vert h) x

end AlgebraicGeometry
