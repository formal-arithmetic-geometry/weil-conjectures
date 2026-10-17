/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Perfectness
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.TracePairing

/-!
# Perfectness of the line-valued Poincaré pairings over a field

The untwisted smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)` of a Tate orientation is a counit, so the
untwisted derived Poincaré pairing `Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)` is perfect once the
value line `Λ_Y(-d)` is identified with `Λ_Y`, as it can be over a separably closed field. Its
degreewise parts, the line-valued pairings `H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d)`, are then
perfect over a finite field.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_tateObject_iso_unit_of_isSepClosed`: over a separably
  closed field `Λ_s(m) ≅ Λ_s`.
- `AlgebraicGeometry.Etale.TateOrientation.bijective_comp_untwistedSmoothTrace`: the untwisted
  smooth trace is a counit.
- `AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_untwistedPoincarePairing_comp`: the
  untwisted derived pairing, read through `Λ_Y(-d) ≅ Λ_Y`, is perfect.
- `AlgebraicGeometry.Etale.TateOrientation.isPerfPair_untwistedDegreewisePoincarePairing`
  (`thm-pod-degreewise-perfectness-over-a-field`, line-valued form).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Point

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- Over a separably closed field `k`, every Tate twisting object of `s = Spec k` is trivial:
`Λ_s(m) ≅ Λ_s`. The twisting object is a locally constant sheaf placed in degree `0` whose stalk
at the geometric point is `Λ`, and étale sheaves on `Spec k` are determined by their global
sections, which are the stalk. -/
theorem nonempty_tateObject_iso_unit_of_isSepClosed [HasInvertibleExponent Λ (Spec (.of k))]
    (m : ℤ) :
    Nonempty (tateObject Λ (Spec (.of k)) m ≅ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) := by
  obtain ⟨L, -, hfib, ⟨e⟩⟩ :=
    HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) (Spec (.of k)) m
  obtain ⟨f⟩ := hfib k (𝟙 _)
  let F := constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let eΓ : Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≅ F.inv :=
    (constantSheafΓAdj _ _).rightAdjointUniq F.asEquivalence.toAdjunction
  let h : L ≅ F.obj (ModuleCat.of Λ Λ) :=
    (F.asEquivalence.counitIso.app L).symm ≪≫
      F.mapIso ((eΓ.app L).symm ≪≫ ΓIsoSheafFiberOfIsSepClosed L ≪≫ f)
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso h ≪≫
    (unitIsoSingleFunctorConstantSheaf Λ _).symm⟩

end Point

namespace TateOrientation

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y} [HasCompactification a] {d : ℕ}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- **The untwisted smooth trace is a counit.** For a Tate orientation `γ`, every morphism
`(Ra_! U)[2d] ⟶ Λ_Y(-d)` is `(Ra_! z)[2d]` followed by the untwisted smooth trace
(`AlgebraicGeometry.Etale.TateOrientation.untwistedSmoothTrace`) for a unique `z : U ⟶ Λ_X`:
untwisting by the invertible `Λ_Y(d)`, this is the projection formula together with the
adjunction `Ra_! ⊣ Ra^!` read through `γ`. -/
theorem bijective_comp_untwistedSmoothTrace (γ : TateOrientation Λ a d)
    (U : DerivedCategoryModule Λ X) :
    Function.Bijective (fun z : U ⟶ 𝟙_ _ ↦
      ((R(a)_![ModuleCat.{u + 1} Λ]).map z)⟦(2 * d : ℤ)⟧' ≫ γ.untwistedSmoothTrace) := by
  obtain ⟨L'', ⟨e⟩, ⟨e'⟩⟩ := isInvertible_tateObject Λ Y (-d)
  obtain ⟨Ψ, hΨ, hΨeq⟩ := exists_bijective_comp_untwist (ModuleCat.{u + 1} Λ)
    (V := ((R(a)_![ModuleCat.{u + 1} Λ]).obj U)⟦(2 * d : ℤ)⟧) e e'
    (constantComplexIsoTateObjectTensor Y d) γ.twistedSmoothTrace
  obtain ⟨T', ⟨eT⟩, ⟨eT'⟩⟩ := isInvertible_tateObject Λ X d
  have h₂ := bijective_derivedTensor_map_comp_twistedTrace (ModuleCat.{u + 1} Λ) a (2 * d : ℤ)
    eT eT' (leftDerivedUpperStarTateObjectIso a d) γ.smoothTrace
    (bijective_rightDerivedLowerShriek_map_shift_comp_smoothTrace _ a γ.dualizingComplexIso)
    (fun K ↦ ((projectionMap _ a).app K).app (tateObject Λ Y d))
    (fun z ↦ NatTrans.congr_app ((projectionMap _ a).naturality z) _)
    (fun K ↦ hasProjectionFormula_of_finite Λ a K _) U
  have hc : (fun z : U ⟶ 𝟙_ _ ↦
      ((R(a)_![ModuleCat.{u + 1} Λ]).map z)⟦(2 * d : ℤ)⟧' ≫ γ.untwistedSmoothTrace) =
      Ψ ∘ (fun z : U ⟶ 𝟙_ _ ↦ ((derivedTensor _ Y).map
        (((R(a)_![ModuleCat.{u + 1} Λ]).map z)⟦(2 * d : ℤ)⟧')).app (tateObject Λ Y d) ≫
          γ.twistedSmoothTrace) :=
    funext fun z ↦ hΨeq _
  rw [hc]
  exact hΨ.comp h₂

/-- **The untwisted derived Poincaré pairing is perfect.** For a Tate orientation `γ`, every
`K` and an isomorphism `τ : Λ_Y(-d) ≅ Λ_Y` (which exists over a separably closed field,
`AlgebraicGeometry.Etale.nonempty_tateObject_iso_unit_of_isSepClosed`), the untwisted derived
Poincaré pairing `Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)`
(`AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`) followed by `τ` is
perfect. -/
theorem isPerfectPairing_untwistedPoincarePairing_comp (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (τ : tateObject Λ Y (-d) ≅ 𝟙_ _) :
    IsPerfectPairing (γ.untwistedPoincarePairing K ≫ τ.hom) := by
  let F := R(a)_![ModuleCat.{u + 1} Λ]
  have e : γ.untwistedPoincarePairing K ≫ τ.hom = poincarePairingOfTrace a K (2 * d : ℤ)
      ((F.commShiftIso (2 * d : ℤ)).inv.app _ ≫
        ((F.commShiftIso (2 * d : ℤ)).hom.app _ ≫ γ.untwistedSmoothTrace ≫ τ.hom)) := by
    simp only [untwistedPoincarePairing, poincarePairingOfTrace, Category.assoc,
      Iso.inv_hom_id_app_assoc]
  rw [e]
  refine isPerfectPairing_poincarePairingOfTrace _ a K _ _ (fun U ↦ ?_)
    (fun N ↦ hasProjectionFormula_of_finite Λ a K N)
  have hc : (fun z : U ⟶ 𝟙_ _ ↦ F.map (z⟦(2 * d : ℤ)⟧') ≫
      (F.commShiftIso (2 * d : ℤ)).hom.app _ ≫ γ.untwistedSmoothTrace ≫ τ.hom) =
      (fun g ↦ (F.commShiftIso (2 * d : ℤ)).hom.app U ≫ g ≫ τ.hom) ∘
        (fun z : U ⟶ 𝟙_ _ ↦ (F.map z)⟦(2 * d : ℤ)⟧' ≫ γ.untwistedSmoothTrace) := by
    funext z
    simp [Functor.commShiftIso_hom_naturality_assoc]
  rw [hc]
  exact (Iso.homCongr ((F.commShiftIso (2 * d : ℤ)).app U).symm τ).bijective.comp
    (γ.bijective_comp_untwistedSmoothTrace U)

end TateOrientation

section FieldDuality

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] [Finite Λ] [HasTateTwist Λ] {k : Type u}
  [Field k] [IsSepClosed k] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} [HasCompactification a]
  [LocallyOfFiniteType a] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ (Spec (.of k))]
  {d : ℕ}

namespace TateOrientation

/-- Blueprint `thm-pod-degreewise-perfectness-over-a-field`: Degreewise perfectness over a
field (finite-field case, line-valued form).

Let `k` be separably closed, `Λ` a finite field (a finite domain) whose characteristic is
invertible on `X`, `γ` a Tate orientation of `a : X ⟶ Spec k` of relative dimension `d`, with
`a` locally of finite type, and `K ∈ D^b_{ctf}(X, Λ)`. Then for `i + j = 2d` the line-valued
Poincaré pairing

`⟨-, -⟩^{untw}_i : H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)`

(`AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing`, read in `Λ`
through any linear isomorphism `ℓ : Λ(-d) ≃ Λ`) is perfect.

The untwisted derived pairing is perfect after identifying `Λ_s(-d)` with `Λ_s`
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_untwistedPoincarePairing_comp`), and
the argument of `AlgebraicGeometry.Etale.TateOrientation.isPerfPair_degreewisePoincarePairing`
applies. -/
theorem isPerfPair_untwistedDegreewisePoincarePairing (γ : TateOrientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (i j : ℤ) (hij : i + j = 2 * d)
    (ℓ : (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ tateObject Λ (Spec (.of k)) (-d)) ≃ₗ[Λ]
      Λ) :
    ((γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).IsPerfPair := by
  obtain ⟨τ⟩ := nonempty_tateObject_iso_unit_of_isSepClosed Λ (k := k) (-(d : ℤ))
  obtain ⟨g, hg⟩ :=
    (γ.isPerfectPairing_untwistedPoincarePairing_comp K τ).exists_addEquiv_degreeZero
      i (j - 2 * d) (by omega)
  have hC : Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))) :=
    finite_compactlySupportedCohomology Λ a K hK i
  obtain ⟨h₀, h₁, h₂⟩ := nondegenerate_comp_unit_shift_of_isSepClosed _ i hC
  let s := (shiftFunctorAdd' (DerivedCategoryModule Λ (Spec (.of k))) (2 * d : ℤ) (j - 2 * d) j
    (by omega)).app ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual _ X).obj (op K)))
  refine LinearMap.isPerfPair_of_comp (Finite.isField_of_domain Λ) _ (fun y ↦ g (y ≫ s.hom))
    (g.bijective.comp ⟨fun y y' h ↦ (cancel_mono s.hom).1 h, fun z ↦ ⟨z ≫ s.inv, by simp⟩⟩)
    (by simp) (fun z ↦ ℓ (z ≫ τ.inv)) (fun z hz ↦ ?_) (fun x y ↦ ?_) h₁ h₂
  · have : z ≫ τ.inv = 0 := ℓ.injective (hz.trans ℓ.map_zero.symm)
    simpa using congrArg (· ≫ τ.hom) this
  · rw [LinearMap.compr₂_apply, LinearEquiv.coe_coe]
    congr 1
    rw [Iso.eq_comp_inv, untwistedDegreewisePoincarePairing_apply]
    have hn : (shiftFunctorZero' (DerivedCategoryModule Λ (Spec (.of k))) (i + (j - 2 * d))
        (by omega)).hom.app (tateObject Λ (Spec (.of k)) (-d)) ≫ τ.hom =
        τ.hom⟦i + (j - 2 * d)⟧' ≫ (shiftFunctorZero' (DerivedCategoryModule Λ (Spec (.of k)))
          (i + (j - 2 * d)) (by omega)).hom.app _ :=
      ((shiftFunctorZero' _ _ _).hom.naturality τ.hom).symm
    rw [Category.assoc, hn, ← Category.assoc, ← degreewisePairing_comp, degreewisePairing_apply]
    simp only [Category.assoc]
    rw [hg x]
    rfl

end TateOrientation

end FieldDuality

end Etale

end AlgebraicGeometry
