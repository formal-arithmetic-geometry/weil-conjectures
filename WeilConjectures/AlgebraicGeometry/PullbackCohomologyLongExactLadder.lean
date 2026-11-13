/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Pullback and the long exact sequence of etale cohomology

We use the existing `Sheaf.H` and `Etale.cohomologyMap` encoding of cohomology and pullback.

## Implementation details

The boundary is postcomposition with `hS.extClass`.
Its derived morphism is exactly `hS.singleδ` (`ShortExact.extClass_hom`), not an
arbitrary choice of a connecting morphism. Identifying Ext cohomology with derived
global sections identifies this boundary with cohomology of the shifted `RΓ(singleδ)`.

## References

* [Stacks, Tag 01FT] (Cohomology on Sites), [Stacks, Tag 010S] (Homology),
  [Stacks, Tag 04I0], [Stacks, Tag 0A5C] (Étale Cohomology)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Etale

/-- Pullback takes a short exact sequence to a short exact sequence, and its cohomology
maps give a commuting ladder of the two long exact sequences, including the initial zero.
(Stacks, Tags 01FT, 010S, 04I0, 0A5C) -/
theorem pullbackCohomology_longExact_ladder {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) :
    ∃ hY : (S.map ((f)^*[AddCommGrpCat.{u + 1}])).ShortExact,
    ∃ δX : ∀ q : ℕ, Sheaf.H S.X₃ q →+ Sheaf.H S.X₁ (q + 1),
    ∃ δY : ∀ q : ℕ,
      Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj S.X₃) q →+
        Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj S.X₁) (q + 1),
      (∀ (q : ℕ) (x : Sheaf.H S.X₃ q), δX q x = x.comp hS.extClass rfl) ∧
      (∀ (q : ℕ) (x : Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj S.X₃) q),
        δY q x = x.comp hY.extClass rfl) ∧
      Function.Injective (Sheaf.H.map S.f 0) ∧
      Function.Injective (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.f) 0) ∧
      (∀ q : ℕ,
        Function.Exact (Sheaf.H.map S.f q) (Sheaf.H.map S.g q) ∧
        Function.Exact (Sheaf.H.map S.g q) (δX q) ∧
        Function.Exact (δX q) (Sheaf.H.map S.f (q + 1))) ∧
      (∀ q : ℕ,
        Function.Exact (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.f) q)
          (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.g) q) ∧
        Function.Exact (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.g) q) (δY q) ∧
        Function.Exact (δY q)
          (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.f) (q + 1))) ∧
      (∀ (q : ℕ) (x : Sheaf.H S.X₁ q),
        cohomologyMap f S.X₂ q (Sheaf.H.map S.f q x) =
          Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.f) q
            (cohomologyMap f S.X₁ q x)) ∧
      (∀ (q : ℕ) (x : Sheaf.H S.X₂ q),
        cohomologyMap f S.X₃ q (Sheaf.H.map S.g q x) =
          Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.g) q
            (cohomologyMap f S.X₂ q x)) ∧
      (∀ (q : ℕ) (x : Sheaf.H S.X₃ q),
        cohomologyMap f S.X₁ (q + 1) (δX q x) = δY q (cohomologyMap f S.X₃ q x)) := by
  have hY := hS.map_of_exact ((f)^*[AddCommGrpCat.{u + 1}])
  have := hS.mono_f
  have := hY.mono_f
  refine ⟨hY, Sheaf.H.δSucc hS, Sheaf.H.δSucc hY, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro q x
    rfl
  · intro q x
    rfl
  · exact Ext.postcomp_mk₀_injective_of_mono _ S.f
  · exact Ext.postcomp_mk₀_injective_of_mono _ (((f)^*[AddCommGrpCat.{u + 1}]).map S.f)
  · intro q
    exact ⟨Sheaf.H.exact_map_map hS q, Sheaf.H.exact_map_δSucc hS q,
      Sheaf.H.exact_δSucc_map hS q⟩
  · intro q
    exact ⟨Sheaf.H.exact_map_map hY q, Sheaf.H.exact_map_δSucc hY q,
      Sheaf.H.exact_δSucc_map hY q⟩
  · intro q x
    exact cohomologyMap_map f q S.f x
  · intro q x
    exact cohomologyMap_map f q S.g x
  · intro q x
    change cohomologyMap f S.X₁ (q + 1) (x.comp hS.extClass rfl) =
      (cohomologyMap f S.X₃ q x).comp hY.extClass rfl
    rw [cohomologyMap_apply,
      cohomologyMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
    exact (Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega)).symm

end AlgebraicGeometry.Etale
