/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SplitTorsor
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Isotypic components of pushforwards along split torsors of Weil sheaves

Let `π : W ⟶ Z` be an étale morphism of `k₀`-schemes and `τ_g`, `g ∈ G`, automorphisms of `W`
over `Z` and over `k₀`, forming a torsor under the finite abelian group `G` which is split by
the `τ_g` (`AlgebraicGeometry.ProEtale.IsTorsorSplit`). The group acts on the pushforward
`P = π_* ℚ̄_ℓ` of the constant pro-étale Weil sheaf by morphisms of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.torsorTranslation`), and for a character `χ` of `G` the
endomorphism `e_χ = |G|⁻¹ ∑_g χ(-g) σ_g` (`AlgebraicGeometry.ProEtaleWeilSheaf.torsorIdempotent`)
projects onto the `χ`-isotypic component.

The main result (`AlgebraicGeometry.ProEtaleWeilSheaf.exists_retraction_of_isotypic`) is the
Weil version of `AlgebraicGeometry.Etale.isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent`:
a morphism of pro-étale Weil sheaves `φ : M ⟶ P` on which `G` acts through `χ` and whose adjoint
`π^* M ⟶ ℚ̄_ℓ` is an isomorphism identifies `M` with the image of `e_χ`: there is a morphism of
pro-étale Weil sheaves `r : P ⟶ M` with `φ ≫ r = 𝟙` and `r ≫ φ = e_χ`. After pullback along the
cover `π` this is checked on the evaluations along the sections of the torsor, which are jointly
injective (`AlgebraicGeometry.ProEtale.torsorEval_hom_ext`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/-- Let `ev_i : F P ⟶ U` be a jointly monomorphic family, `φ : M ⟶ P` such that
`F φ ≫ ev_i = θ ≫ s_i` for an isomorphism `θ`, and `e : P ⟶ P` such that `F e ≫ ev_i = a ≫ s_i`
for some `a`. Then `F e` factors through `F φ`. -/
lemma Functor.map_eq_comp_of_jointlyMono {ι : Type*} {P M : C} {U : D}
    (ev : ι → (F.obj P ⟶ U))
    (hev : ∀ {T : D} (a b : T ⟶ F.obj P), (∀ i, a ≫ ev i = b ≫ ev i) → a = b)
    (s : ι → (U ⟶ U)) (e : P ⟶ P) (a : F.obj P ⟶ U) (φ : M ⟶ P) (θ : F.obj M ⟶ U) [IsIso θ]
    (he : ∀ i, F.map e ≫ ev i = a ≫ s i) (hφ : ∀ i, F.map φ ≫ ev i = θ ≫ s i) :
    F.map e = a ≫ CategoryTheory.inv θ ≫ F.map φ :=
  hev _ _ fun i ↦ by
    rw [he, Category.assoc, Category.assoc, hφ i, IsIso.inv_hom_id_assoc]

/-- In the situation of `CategoryTheory.Functor.map_eq_comp_of_jointlyMono`, with `C` abelian,
`F` faithful and additive and `s_{i₀} = 𝟙`, the morphism `φ` is a monomorphism and `e` factors
through it. -/
lemma Functor.mono_and_comp_cokernel_eq_zero_of_jointlyMono [Abelian C] [Preadditive D]
    [F.Additive] [F.Faithful] {ι : Type*} {P M : C} {U : D} (ev : ι → (F.obj P ⟶ U))
    (hev : ∀ {T : D} (a b : T ⟶ F.obj P), (∀ i, a ≫ ev i = b ≫ ev i) → a = b)
    (s : ι → (U ⟶ U)) (i₀ : ι) (hs : s i₀ = 𝟙 U) (e : P ⟶ P) (a : F.obj P ⟶ U) (φ : M ⟶ P)
    (θ : F.obj M ⟶ U) [IsIso θ]
    (he : ∀ i, F.map e ≫ ev i = a ≫ s i) (hφ : ∀ i, F.map φ ≫ ev i = θ ≫ s i) :
    Mono φ ∧ e ≫ cokernel.π φ = 0 := by
  have h := F.map_eq_comp_of_jointlyMono ev hev s e a φ θ he hφ
  refine ⟨?_, F.map_injective ?_⟩
  · have : Mono (F.map φ) := by
      have hsplit : F.map φ ≫ ev i₀ ≫ CategoryTheory.inv θ = 𝟙 _ := by
        rw [← Category.assoc, hφ, hs, Category.comp_id, IsIso.hom_inv_id]
      exact (IsSplitMono.mk' ⟨_, hsplit⟩).mono
    exact F.mono_of_mono_map this
  · rw [F.map_comp, h, Category.assoc, Category.assoc, ← F.map_comp, cokernel.condition,
      F.map_zero, Functor.map_zero, comp_zero, comp_zero]

end CategoryTheory

namespace AlgebraicGeometry

open scoped ProEtale

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The pullback commutes with multiplication by a scalar. -/
lemma AdicSheaf.adicUpperStar_map_smul {X Z : Scheme.{u}} (g : X ⟶ Z)
    (c : ULift.{u + 1} (PadicAlgCl l)) (M : AdicSheaf l Z) :
    (g)^*ᵃ[l].map (AdicSheaf.smul c M) = AdicSheaf.smul c ((g)^*ᵃ[l].obj M) := by
  apply ((adicUpperStarLowerStarAdjunction l g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← Functor.comp_map,
    ← (adicUpperStarLowerStarAdjunction l g).unit.naturality, Functor.id_map,
    AdicSheaf.adicLowerStar_map_smul]
  exact AdicSheaf.smul_comp c _

/-- A morphism of sheaves of `ℚ̄_ℓ,Z`-modules vanishes if its pullback along a quasi-compact
surjective weakly étale morphism does: its image vanishes, being detected on the pullback
(`AlgebraicGeometry.ProEtale.AdicSheaf.isZero_of_isZero_upperStar`). -/
lemma AdicSheaf.eq_zero_of_adicUpperStar_map_eq_zero {W Z : Scheme.{u}} (π : W ⟶ Z)
    [WeaklyEtale π] [QuasiCompact π] [Surjective π] {A B : AdicSheaf l Z} (h : A ⟶ B)
    (hh : (π)^*ᵃ[l].map h = 0) : h = 0 := by
  have hz : IsZero (Abelian.image h) := by
    refine AdicSheaf.isZero_of_isZero_upperStar (fun _ : PUnit.{u + 1} ↦ π) ?_ fun _ ↦ ?_
    · rw [Presieve.ofArrows_pUnit]
      exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
    · refine IsZero.of_iso ?_ (Abelian.PreservesImage.iso (π)^*ᵃ[l] h)
      have : Abelian.factorThruImage ((π)^*ᵃ[l].map h) = 0 := by
        rw [← cancel_mono (Abelian.image.ι _), Abelian.image.fac, zero_comp]
        exact hh
      exact IsZero.of_epi_eq_zero _ this
  rw [← Abelian.image.fac h, hz.eq_of_src (Abelian.image.ι h) 0, comp_zero]

/-- The pullback along a quasi-compact surjective weakly étale morphism is faithful. -/
lemma AdicSheaf.faithful_adicUpperStar {W Z : Scheme.{u}} (π : W ⟶ Z) [WeaklyEtale π]
    [QuasiCompact π] [Surjective π] : (π)^*ᵃ[l].Faithful where
  map_injective {A B} f g hfg := by
    rw [← sub_eq_zero]
    exact AdicSheaf.eq_zero_of_adicUpperStar_map_eq_zero π _
      (by rw [Functor.map_sub, hfg, sub_self])

end ProEtale

end AlgebraicGeometry
