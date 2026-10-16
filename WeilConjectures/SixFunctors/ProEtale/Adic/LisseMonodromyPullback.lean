/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy

/-!
# Monodromy of lisse sheaves and pullback

Let `f : Y' ⟶ Y` be a morphism of connected schemes. The monodromies of lisse `ℓ`-adic sheaves
on `Y` and `Y'` (`AlgebraicGeometry.ProEtale.LisseMonodromy`) are *compatible* with `f`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.IsCompatible`) if, under the identification
`G_{y ≫ f} = (f^* G)_y` of stalks, the transport along the path `F_{y ≫ f} ≅ F_{z ≫ f}` induced by
a path `τ : F_y ≅ F_z` of `Y'` is the transport along `τ` on `Y'`: the monodromy representation
of `π₁(Y', y)` on `(f^* G)_y` is that of `π₁(Y, y ≫ f)` on `G_{y ≫ f}`, restricted along the map
of fundamental groups. This is the compatibility of `cor-galois-lisse-representations` with base
change of finite étale covers (`thm-galois-fundamental`); its existence, for connected regular
locally Noetherian schemes, is `AlgebraicGeometry.ProEtale.exists_lisseMonodromy_isCompatible`.

If moreover `π₁(Y') → π₁(Y)` is surjective, a lisse subsheaf `G'` of `f^* N` for a lisse `N`
on `Y` is the pullback of a lisse sheaf on `Y`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_injective`): its stalk is a
`π₁(Y')`-stable, hence `π₁(Y)`-stable, subspace of `N_{y ≫ f}`.

## Main statements

- `AlgebraicGeometry.ProEtale.LisseMonodromy.IsCompatible`: compatibility of monodromies with a
  morphism.
- `AlgebraicGeometry.ProEtale.exists_lisseMonodromy_isCompatible`: compatible monodromies exist.
- `AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_injective`: lisse subsheaves
  of pullbacks descend along a morphism surjective on fundamental groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme.FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {Ω : Type u} [Field Ω]

namespace LisseMonodromy

/-- The monodromies `M` on `Y` and `M'` on `Y'` are *compatible* with `f : Y' ⟶ Y` if the
transport along the path `F_{y ≫ f} ≅ F_{z ≫ f}` induced by a path `τ : F_y ≅ F_z` of `Y'` is,
under the identifications `G_{y ≫ f} = (f^* G)_y`, the transport along `τ` of the pullback. -/
def IsCompatible (f : Y' ⟶ Y) (M : LisseMonodromy l Y Ω) (M' : LisseMonodromy l Y' Ω) : Prop :=
  ∀ ⦃y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'⦄ (τ : fiber y ≅ fiber z) (G : LisseSheaf l Y),
    (M.mono (pullbackPathIso f τ)).hom.app G ≫ (upperStarStalkIso l f z G.obj.X).hom =
      (upperStarStalkIso l f y G.obj.X).hom ≫ (M'.mono τ).hom.app (G.upperStar l f)

/-- The `ℚ̄_ℓ`-linear identification `G_{y ≫ f} ≅ (f^* G)_y` of stalks. -/
noncomputable abbrev upperStarStalkLinearEquiv (f : Y' ⟶ Y)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y') (G : LisseSheaf l Y) :
    StalkSpace (y ≫ f) G ≃ₗ[PadicAlgCl l] StalkSpace y (G.upperStar l f) :=
  WeilCoefficients.linearEquivOfIso (upperStarStalkIso l f y G.obj.X)

variable {f : Y' ⟶ Y} {M : LisseMonodromy l Y Ω} {M' : LisseMonodromy l Y' Ω}

/-- For compatible monodromies, the identification `G_{y ≫ f} ≅ (f^* G)_y` intertwines the
action of `π₁(Y', y)` on `(f^* G)_y` with that of its image in `π₁(Y, y ≫ f)` on `G_{y ≫ f}`. -/
lemma IsCompatible.rep_apply (hc : IsCompatible f M M')
    {y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'} (σ : Aut (fiber y)) (G : LisseSheaf l Y)
    (v : StalkSpace (y ≫ f) G) :
    upperStarStalkLinearEquiv f y G (M.rep (y ≫ f) G (pullbackPathIso f σ) v) =
      M'.rep y (G.upperStar l f) σ (upperStarStalkLinearEquiv f y G v) := by
  have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v) (hc σ G)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The stalks of a lisse sheaf at geometric points are finite-dimensional. -/
instance finiteDimensional_stalkSpace (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (G : LisseSheaf l Y) : FiniteDimensional (PadicAlgCl l) (StalkSpace t G) :=
  (G.property.upperStar t).isAdicConstructibleSheaf.finiteDimensional_globalSections

/-- **Lisse subsheaves of pullbacks descend.** Let `M`, `M'` be monodromies on `Y`, `Y'`
compatible with `f : Y' ⟶ Y`, which are equivalences at `t ≫ f` and `t`, and assume that every
automorphism of `F_{t ≫ f}` is induced by one of `F_t` (`π₁(Y', t) → π₁(Y, t ≫ f)` is
surjective). Let `N` be lisse on `Y` and `i : G' ⟶ f^* N` a morphism of lisse sheaves on `Y'`
which is injective on stalks at `t`. Then `G'` is the pullback of a lisse sheaf on `Y`: the image
of `G'_t` in `(f^* N)_t = N_{t ≫ f}` is `π₁(Y')`-stable, hence `π₁(Y)`-stable, hence the stalk
of a lisse sheaf `G` on `Y`, and `f^* G ≅ G'` since both have the same `π₁(Y')`-representation. -/
theorem exists_upperStar_iso_of_injective {t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'}
    (hM : M.IsEquivalenceAt (t ≫ f)) (hM' : M'.IsEquivalenceAt t) (hc : IsCompatible f M M')
    (hsurj : ∀ σ : Aut (fiber (t ≫ f)), ∃ σ' : Aut (fiber t), pullbackPathIso f σ' = σ)
    {N : LisseSheaf l Y} {G' : LisseSheaf l Y'} (i : G' ⟶ N.upperStar l f)
    (hi : Function.Injective ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map i)).hom) :
    ∃ G : LisseSheaf l Y, Nonempty (G.upperStar l f ≅ G') := by
  set ι := ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map i)).hom
  set e₀ := upperStarStalkLinearEquiv f t N
  let W : Subrepresentation (M.rep (t ≫ f) N) :=
    { toSubmodule := (LinearMap.range ι).comap e₀.toLinearMap
      apply_mem_toSubmodule σ b hb := by
        obtain ⟨σ', rfl⟩ := hsurj σ
        obtain ⟨g, hg⟩ := hb
        refine ⟨M'.rep t G' σ' g, ?_⟩
        rw [LinearEquiv.coe_toLinearMap, hc.rep_apply, ← LinearEquiv.coe_toLinearMap, ← hg]
        exact M'.rep_naturality t i σ' g }
  obtain ⟨G, eG, heG⟩ := hM.essSurj W.toSubmodule W.toRepresentation fun φ w ↦ by
    obtain ⟨φ', hφ'⟩ := LinearMap.exists_extend (K := PadicAlgCl l) (p := W.toSubmodule) φ
    have h (σ : Aut (fiber (t ≫ f))) : φ (W.toRepresentation σ w) = φ' (M.rep _ N σ w) := by
      rw [← hφ']
      rfl
    simp_rw [h]
    exact hM.continuous_rep N φ' w
  -- the image of `G'_t` in `(f^* N)_t`
  have key (x : LinearMap.range ι) : ι ((LinearEquiv.ofInjective ι hi).symm x) = x := by
    rw [← LinearEquiv.ofInjective_apply ι (h := hi), LinearEquiv.apply_symm_apply]
  let ψ : StalkSpace t (G.upperStar l f) →ₗ[PadicAlgCl l] StalkSpace t G' :=
    (LinearEquiv.ofInjective ι hi).symm.toLinearMap ∘ₗ
      ((e₀.toLinearMap ∘ₗ W.toSubmodule.subtype).codRestrict (LinearMap.range ι) fun w ↦ w.2) ∘ₗ
      eG.toLinearMap ∘ₗ (upperStarStalkLinearEquiv f t G).symm.toLinearMap
  have hψ (v) : ι (ψ v) = e₀ (eG ((upperStarStalkLinearEquiv f t G).symm v)) :=
    key _
  have hψinj : Function.Injective ψ := fun v w h ↦ by
    have := congrArg ι h
    rw [hψ, hψ] at this
    exact (upperStarStalkLinearEquiv f t G).symm.injective
      (eG.injective (Subtype.ext (e₀.injective this)))
  have hψsurj : Function.Surjective ψ := fun g ↦ by
    obtain ⟨w, hw⟩ := eG.surjective ⟨e₀.symm (ι g), g, (e₀.apply_symm_apply (ι g)).symm⟩
    refine ⟨upperStarStalkLinearEquiv f t G w, hi ?_⟩
    rw [hψ, LinearEquiv.symm_apply_apply, hw, LinearEquiv.apply_symm_apply]
  obtain ⟨φ, hφ⟩ := hM'.full ψ fun σ v ↦ hi (by
    rw [hψ, M'.rep_naturality t i σ, hψ]
    obtain ⟨v, rfl⟩ := (upperStarStalkLinearEquiv f t G).surjective v
    rw [← hc.rep_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, heG,
      ← hc.rep_apply]
    rfl)
  have := hM'.isIso_of_bijective φ (by rw [hφ]; exact ⟨hψinj, hψsurj⟩)
  exact ⟨G, ⟨asIso φ⟩⟩

end LisseMonodromy

end AlgebraicGeometry.ProEtale
