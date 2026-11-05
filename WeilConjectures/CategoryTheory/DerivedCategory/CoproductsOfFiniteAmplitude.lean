/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Commutation with coproducts from the bounded case

Let `G : D(C) ⥤ D(D)` be a triangulated functor and `𝓔` a triangulated subcategory of `D(C)`
stable under the truncations and under coproducts. Suppose that `G` has *finite amplitude on
`𝓔`*: it does not lower degrees, and sends objects of `𝓔` in degrees `≤ b` into degrees
`≤ b + e`. If `G` commutes with coproducts of uniformly bounded families of objects of `𝓔`, then
it commutes with all coproducts of families of objects of `𝓔`
(`DerivedCategory.isIso_sigmaComparison_of_bounded`).

Indeed, `Hᵐ(G M)` only depends on the truncation `τ_{[m - e, m]} M`: the map
`Hᵐ(G(τ_{≤ m} M)) ⟶ Hᵐ(G M)` is an isomorphism because `G(τ_{> m} M)` lies in degrees `> m`, and
`Hᵐ(G(τ_{≤ m} M)) ⟶ Hᵐ(G(τ_{≥ m - e} τ_{≤ m} M))` is an isomorphism because
`G(τ_{< m - e} τ_{≤ m} M)` lies in degrees `< m`. Truncations commute with coproducts, the
cohomology functors commuting with exact coproducts.

This is the formal part of the comparison of blueprint `lem-exc-direct-image-coproducts`, in
the form used for the finite-coefficient localizing categories of blueprint
`det-sf-comp-coherence-single`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

open TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` in `D(C)`, if `Hᵏ(X₁) ⟶ Hᵏ(X₂)` is
an epimorphism and `Hᵏ⁺¹(X₁) ⟶ Hᵏ⁺¹(X₂)` a monomorphism, then `Hᵏ(X₃) = 0`. -/
lemma isZero_homology_obj₃_of_epi_of_mono (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (k : ℤ) (h₁ : Epi ((homologyFunctor C k).map T.mor₁))
    (h₂ : Mono ((homologyFunctor C (k + 1)).map T.mor₁)) :
    IsZero ((homologyFunctor C k).obj T.obj₃) :=
  (HomologySequence.exact₃ T hT k (k + 1) rfl).isZero_X₂
    ((HomologySequence.epi_homologyMap_mor₁_iff T hT k).1 h₁)
    ((HomologySequence.mono_homologyMap_mor₁_iff T hT k (k + 1) rfl).1 h₂)

variable [Abelian.HasKInjectiveResolutions C] {J : Type*} [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C]

/-- A coproduct of objects in degrees `≤ b` lies in degrees `≤ b`. -/
lemma isLE_sigma (X : J → DerivedCategory C) (b : ℤ) (hX : ∀ j, (X j).IsLE b) :
    (∐ X).IsLE b := by
  rw [isLE_iff]
  intro i hi
  have hc := isColimitOfPreserves (homologyFunctor C i) (coproductIsCoproduct X)
  refine (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun j ↦ ?_)
  exact (isZero_of_isLE _ b i hi (hX := hX j.as)).eq_of_src _ _

/-- The cohomology of a coproduct of morphisms is an isomorphism if the cohomology of each
morphism is. -/
lemma isIso_homologyFunctor_map_sigmaMap {X Y : J → DerivedCategory C} (φ : ∀ j, X j ⟶ Y j)
    (k : ℤ) (h : ∀ j, IsIso ((homologyFunctor C k).map (φ j))) :
    IsIso ((homologyFunctor C k).map (Limits.Sigma.map φ)) := by
  have e : (homologyFunctor C k).map (Limits.Sigma.map φ) =
      inv (sigmaComparison (homologyFunctor C k) X) ≫
        Limits.Sigma.map (fun j ↦ (homologyFunctor C k).map (φ j)) ≫
          sigmaComparison (homologyFunctor C k) Y := by
    rw [IsIso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp [← Functor.map_comp]
  rw [e]
  infer_instance

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions D] [HasColimitsOfShape (Discrete J) D]
  [HasExactColimitsOfShape (Discrete J) D]

omit [HasExactColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) D] in
/-- The comparison maps `∐ G(Xⱼ) ⟶ G(∐ Xⱼ)` are natural in the family `Xⱼ`. -/
@[reassoc]
lemma sigmaComparison_naturality (G : DerivedCategory C ⥤ DerivedCategory D)
    {X Y : J → DerivedCategory C} (φ : ∀ j, X j ⟶ Y j) :
    sigmaComparison G X ≫ G.map (Limits.Sigma.map φ) =
      Limits.Sigma.map (fun j ↦ G.map (φ j)) ≫ sigmaComparison G Y := by
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  simp [← Functor.map_comp]

end DerivedCategory
