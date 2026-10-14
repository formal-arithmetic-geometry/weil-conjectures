/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk

/-!
# Descent of trivialisations along a pro-étale cover

Let `f : W ⟶ T` be a single-morphism pro-étale cover (weakly étale, surjective and
quasi-compact) and `M` an `ℓ`-adic sheaf on `T`. A trivialisation `ε : f^* M ≅ ℚ̄_ℓ,Wⁿ` whose
transition matrix on `W ×_T W` is the identity descends to a trivialisation `M ≅ ℚ̄_ℓ,Tⁿ`
(`AlgebraicGeometry.ProEtale.AdicSheaf.nonempty_iso_of_transitionMatrix_eq_one`).

The input is the sheaf property of `M` for the cover `f`, in the form of the descent of
morphisms `ℚ̄_ℓ ⟶ M` out of the unit, i.e. of global sections
(`AlgebraicGeometry.ProEtale.AdicSheaf.exists_upperStar_map_eq_of_cover`): the descended
morphisms `ℚ̄_ℓ,T ⟶ M` assemble to `ℚ̄_ℓ,Tⁿ ⟶ M`, whose pullback along `f` is `ε⁻¹`, hence is an
isomorphism, pullback along a cover being conservative.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {T W : Scheme.{u}}

/-- **Descent of morphisms out of the unit along a pro-étale cover.** Let `f : W ⟶ T` be weakly
étale, surjective and quasi-compact, and `M` an `ℓ`-adic sheaf on `T`. A morphism
`v : ℚ̄_ℓ,W ⟶ f^* M` whose two pullbacks to `W ×_T W` agree (under
`p₁^* f^* M ≅ (p₁ ≫ f)^* M = (p₂ ≫ f)^* M ≅ p₂^* f^* M`) is the pullback of a morphism
`ℚ̄_ℓ,T ⟶ M`. Equivalently (`AlgebraicGeometry.ProEtale.bijective_globalSectionOfModHom`), a
global section of `f^* M` whose two restrictions to `W ×_T W` agree comes from a global section
of `M`: this is the sheaf condition of `M` for the covering `{W ⟶ T}` of the pro-étale site,
the global sections of `f^* M` being the sections of `M` over `W`, `f` being weakly étale
(Stacks Project, Tag 00VM, for the sheaf condition; Bhatt–Scholze, *The pro-étale topology for
schemes*, §4.1, for the pro-étale site). -/
theorem exists_upperStar_map_eq_of_cover (f : W ⟶ T) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {M : AdicSheaf l T} (v : unit l W ⟶ (f)^*ᵃ[l].obj M)
    (hv : (adicUpperStarUnitIso l (pullback.fst f f)).inv ≫ (pullback.fst f f)^*ᵃ[l].map v ≫
        (adicUpperStarCompIso l (pullback.condition (f := f) (g := f))).hom.app M =
      (adicUpperStarUnitIso l (pullback.snd f f)).inv ≫ (pullback.snd f f)^*ᵃ[l].map v) :
    ∃ w : unit l T ⟶ M, (adicUpperStarUnitIso l f).inv ≫ (f)^*ᵃ[l].map w = v := by
  sorry

/-- **Descent of trivialisations.** Let `f : W ⟶ T` be weakly étale, surjective and
quasi-compact, `M` an `ℓ`-adic sheaf on `T` and `ε : f^* M ≅ ℚ̄_ℓ,Wⁿ` a trivialisation whose
transition matrix on `W ×_T W` is the identity. Then `M ≅ ℚ̄_ℓ,Tⁿ`. -/
theorem nonempty_iso_of_transitionMatrix_eq_one (f : W ⟶ T) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {M : AdicSheaf l T} {n : ℕ}
    (ε : (f)^*ᵃ[l].obj M ≅ ⨁ fun _ : Fin n ↦ unit l W)
    (hε : transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition = 1) :
    Nonempty (M ≅ ⨁ fun _ : Fin n ↦ unit l T) := by
  have hι (g : W ⟶ T) (i : Fin n) :
      biproduct.ι (fun _ : Fin n ↦ unit l W) i ≫ (freeUpperStarIso l (Fin n) g).inv =
        (adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map (biproduct.ι _ i) := by
    simp [freeUpperStarIso]
  have hι' {P : Scheme.{u}} (g : P ⟶ W) (i : Fin n) :
      biproduct.ι (fun _ : Fin n ↦ unit l P) i ≫ (freeUpperStarIso l (Fin n) g).inv =
        (adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map (biproduct.ι _ i) := by
    simp [freeUpperStarIso]
  -- the transition isomorphism is the identity
  have htr : (transitionIso ε (pullback.fst f f) (pullback.snd f f) pullback.condition).hom =
      𝟙 _ := by
    apply unitMatrix_injective
    rw [← transitionMatrix, hε, unitMatrix_id]
  have htr' : (trivPull f ε (pullback.fst f f)).inv ≫
      (adicUpperStarCongr l (pullback.condition (f := f) (g := f))).hom.app M =
        (trivPull f ε (pullback.snd f f)).inv := by
    rw [← cancel_mono (trivPull f ε (pullback.snd f f)).hom, Iso.inv_hom_id, Category.assoc]
    simpa [transitionIso] using htr
  -- the columns of `ε⁻¹` descend
  have hdesc (i : Fin n) : ∃ w : unit l T ⟶ M, (adicUpperStarUnitIso l f).inv ≫
      (f)^*ᵃ[l].map w = biproduct.ι (fun _ : Fin n ↦ unit l W) i ≫ ε.inv := by
    refine exists_upperStar_map_eq_of_cover f _ ?_
    have hp (p : pullback f f ⟶ W) : biproduct.ι (fun _ : Fin n ↦ unit l (pullback f f)) i ≫
        (trivPull f ε p).inv = (adicUpperStarUnitIso l p).inv ≫
          (p)^*ᵃ[l].map (biproduct.ι (fun _ : Fin n ↦ unit l W) i ≫ ε.inv) ≫
            (adicUpperStarComp l p f).inv.app M := by
      simp only [trivPull, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Functor.map_comp,
        Category.assoc]
      rw [reassoc_of% hι' p i]
    rw [← hp, ← hp, ← htr']
    simp only [adicUpperStarCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rfl
  choose w hw using hdesc
  let φ : (⨁ fun _ : Fin n ↦ unit l T) ⟶ M := biproduct.desc w
  have hφ : (freeUpperStarIso l (Fin n) f).inv ≫ (f)^*ᵃ[l].map φ = ε.inv := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [reassoc_of% hι f i, ← Functor.map_comp, biproduct.ι_desc, hw]
  have : IsIso ((f)^*ᵃ[l].map φ) := by
    rw [show (f)^*ᵃ[l].map φ = (freeUpperStarIso l (Fin n) f).hom ≫ ε.inv by
      rw [← hφ, Iso.hom_inv_id_assoc]]
    infer_instance
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ W) (fun _ ↦ f) ∈ Scheme.proetalePrecoverage T := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
  have : IsIso φ := isIso_of_isIso_adicUpperStar l (fun _ : Unit ↦ f) hcov φ fun _ ↦ this
  exact ⟨(asIso φ).symm⟩

end AlgebraicGeometry.ProEtale.AdicSheaf
