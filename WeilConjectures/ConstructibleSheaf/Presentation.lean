/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Constructible sheaves are quotients of sums of `j_{V!} Λ_V`

On a scheme `X` with Noetherian underlying space and for a finite commutative ring `Λ`, every
constructible sheaf of `Λ`-modules on `X_ét` is a quotient of a finite coproduct `∐ j_{V!} Λ_V`
of extensions by zero of constant sheaves along étale maps `j_V : V ⟶ X` from affine schemes
[Stacks 095M; SGA 4½, Rapport, 4.6].

Here `j_{V!}` is the extension by zero `AlgebraicGeometry.Etale.etaleLowerShriek` along the
étale map `j_V`, the left adjoint of the pullback `j_V^*`. Maps `j_{V!} Λ_V ⟶ G` are sections of
`G` over `V`, as are maps out of the free sheaf `Λ[V]`
(`AlgebraicGeometry.Scheme.etaleLowerShriekConstantSheafHomEquiv`), so the statement is the
generation of constructible sheaves by free sheaves on affine étale `X`-schemes,
`AlgebraicGeometry.Etale.exists_jointlyEpi_freeYoneda`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_epi_sigma_lowerShriek_constantSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- Maps out of the extension by zero `j_! Λ_V` of the constant sheaf along an étale
`j : V ⟶ X` are maps out of the free sheaf `Λ[V]` on the étale `X`-scheme `V`: both are
sections over `V`, by the adjunction `j_! ⊣ j^*` and the adjunction between the constant sheaf
and global sections. -/
noncomputable def etaleLowerShriekConstantSheafHomEquiv {V : Scheme.{u}} (j : V ⟶ X)
    (h : Etale j) (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) j h).obj
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ⟶
      G) ≃
      (Sheaf.freeYoneda X.smallEtaleTopology
        ((MorphismProperty.Over.map ⊤ h).obj (Etale.mk (𝟙 V))) (ModuleCat.of Λ Λ) ⟶ G) :=
  ((Etale.etaleLowerShriekUpperStarAdjunction _ j h).homEquiv _ _).trans <|
    ((constantSheafAdj V.smallEtaleTopology _
      (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _).trans <|
      Sheaf.freeYonedaHomEquiv.symm.trans (Etale.freeYonedaEtaleHomEquiv j h _ G).symm

lemma etaleLowerShriekConstantSheafHomEquiv_comp {V : Scheme.{u}} (j : V ⟶ X) (h : Etale j)
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ψ : (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) j h).obj
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ⟶
      G) (f : G ⟶ G') :
    etaleLowerShriekConstantSheafHomEquiv j h G' (ψ ≫ f) =
      etaleLowerShriekConstantSheafHomEquiv j h G ψ ≫ f := by
  apply (Etale.freeYonedaEtaleHomEquiv j h _ G').injective
  apply Sheaf.freeYonedaHomEquiv.injective
  simp only [etaleLowerShriekConstantSheafHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Etale.freeYonedaEtaleHomEquiv_comp, Etale.freeYonedaHomEquiv_comp,
    Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- **Constructible sheaves are quotients of sums of `j_{V!} Λ_V`** [Stacks 095M; SGA 4½,
Rapport, 4.6]. This is the key input of blueprint `sk-lem-sf-flat-model`.

On a scheme `X` with Noetherian underlying space and for a finite commutative ring `Λ`, every
constructible sheaf `F` of `Λ`-modules on `X_ét` is a quotient of a finite coproduct
`∐ j_{V!} Λ_V`, with `j_V : V ⟶ X` étale, `V` affine and `j_{V!}` the extension by zero along
`j_V` (`AlgebraicGeometry.Etale.etaleLowerShriek`). Each `j_{V!} Λ_V` is the free sheaf `Λ[V]`,
which is flat (`AlgebraicGeometry.Etale.flat_freeYoneda`) and, as `Λ` is finite, constructible
(`AlgebraicGeometry.Etale.isConstructibleSheaf_freeYoneda`). -/
theorem exists_epi_sigma_lowerShriek_constantSheaf [Finite Λ]
    [TopologicalSpace.NoetherianSpace X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (j : ∀ i, V i ⟶ X) (h : ∀ i, Etale (j i)),
      (∀ i, IsAffine (V i)) ∧
      ∃ φ : (∐ fun i ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (j i) (h i)).obj
          ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))) ⟶ F, Epi φ := by
  obtain ⟨n, W, s, hW, hs⟩ := Etale.exists_jointlyEpi_freeYoneda F
  let e (i : Fin n) : (MorphismProperty.Over.map ⊤ (W i).prop).obj (Etale.mk (𝟙 (W i).left)) ≅
      W i :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp; rfl)
  let ψ (i : Fin n) := (etaleLowerShriekConstantSheafHomEquiv (W i).hom (W i).prop F).symm
    ((Etale.freeYonedaMapIso (e i)).hom ≫ s i)
  refine ⟨n, fun i ↦ (W i).left, fun i ↦ (W i).hom, fun i ↦ (W i).prop, hW, Sigma.desc ψ,
    Preadditive.epi_of_cancel_zero _ fun {G} f hf ↦ hs f fun i ↦ ?_⟩
  have h₁ : ψ i ≫ f = 0 := by simpa using Sigma.ι _ i ≫= hf
  have h₂ := congrArg (etaleLowerShriekConstantSheafHomEquiv (W i).hom (W i).prop G) h₁
  have h₀ : etaleLowerShriekConstantSheafHomEquiv (W i).hom (W i).prop G 0 = 0 := by
    simpa using etaleLowerShriekConstantSheafHomEquiv_comp (W i).hom (W i).prop
      (0 : _ ⟶ G) (0 : G ⟶ G)
  rw [etaleLowerShriekConstantSheafHomEquiv_comp, h₀, Equiv.apply_symm_apply,
    Category.assoc] at h₂
  simpa using (Etale.freeYonedaMapIso (e i)).inv ≫= h₂

end AlgebraicGeometry.Scheme
