/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleSmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational

/-!

# Smooth base change for bounded constructible `E`-complexes

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ`. For a cartesian square
```
X' --u--> X
|         |
p'        p
v         v
Y' --v--> Y
```
of separated `k`-schemes of finite type with `v` smooth, the base change map
`Lv^* Rp_* K ⟶ Rp'_* Lu^* K` of `Dᵇc(-)⟦E⟧` is an isomorphism for every bounded constructible
`K` (`ProEtale.CondensedRing.ContinuousMapRingObj.isIso_boundedConstructibleBaseChange_of_smooth`,
blueprint `theorem-smooth-base-change-all-admissible--3`).

As in the blueprint proof, `K` has an integral model `K₀ ∈ Dᵇc(X)⟦𝒪_E⟧`
(`ProEtale.isLocalization_boundedConstructibleExtendScalars`), the extension of scalars of the
integral base change morphism at `K₀` is the `E`-base change morphism at `E ⊗ᴸ_{𝒪_E} K₀`
(`ProEtale.CondensedRing.nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational`),
and the integral base change morphism is invertible by derived Nakayama and finite-coefficient
smooth base change.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ContinuousMapRingObj

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {p : X ⟶ Y} {v : Y' ⟶ Y} {p' : X' ⟶ Y'} {u : X' ⟶ X}

/-- **Smooth base change** for bounded constructible `E`-complexes, `E` a finite extension of
`ℚ_ℓ` inside `ℚ̄_ℓ` (blueprint `theorem-smooth-base-change-all-admissible--3`): for a cartesian
square of separated `k`-schemes of finite type with `v` smooth, the base change map
`Lv^* Rp_* K ⟶ Rp'_* Lu^* K` of `Dᵇc(-)⟦E⟧` is an isomorphism for every bounded constructible
`K`.

The complex `K` is `E ⊗ᴸ_{𝒪_E} K₀` for some `K₀ ∈ Dᵇc(X)⟦𝒪_E⟧`, since the extension of scalars is
a localization functor; the base change morphism at `E ⊗ᴸ_{𝒪_E} K₀` is the extension of scalars
of the integral one at `K₀`
(`nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational`), which derived Nakayama
reduces to its first derived reduction
(`isIso_boundedConstructibleBaseChange_integral_app_of_reduction`), the pro-étale base change
morphism with coefficients `𝔽_E` at a complex of étale origin, invertible by finite-coefficient
smooth base change (`ProEtale.isIso_derivedBaseChangeMap_app_of_smooth`). -/
theorem isIso_boundedConstructibleBaseChange_of_smooth (sq : IsPullback u p' p v)
    [Smooth v.left] (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧) :
    IsIso ((boundedConstructibleBaseChange ℓ E sq.toCommSq).app K) := by
  have hsq : IsPullback u.left p'.left p.left v.left := sq.map (Over.forget _)
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := {}
  have : CompactSpace Y'.left := QuasiCompact.compactSpace_of_compactSpace Y'.hom
  have : IsLocallyNoetherian Y'.left := LocallyOfFiniteType.isLocallyNoetherian Y'.hom
  have : IsNoetherian Y'.left := {}
  have : QuasiCompact (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
  have : QuasiSeparated (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
  have : QuasiCompact p.left := QuasiCompact.of_comp p.left Y.hom
  have : QuasiSeparated p.left := QuasiSeparated.of_comp p.left Y.hom
  have hℓ : IsUnit (ℓ : k) := by
    refine IsUnit.mk0 _ fun h ↦ (Fact.out : ringChar k ≠ ℓ) ?_
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar k).Prime) Fact.out).1
      ((ringChar.spec k ℓ).1 h)
  have hℓY : IsUnit (ℓ : Γ(Y.left, ⊤)) := by
    simpa using (hℓ.map (ΓSpecIso (.of k)).inv.hom).map Y.hom.appTop.hom
  have := Localization.essSurj (boundedConstructibleExtendScalars X.left ℓ E)
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)
  obtain ⟨K₀, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (boundedConstructibleExtendScalars X.left ℓ E) K
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  obtain ⟨α⟩ := nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational ℓ E
    sq.toCommSq K₀
  have : IsIso ((PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E.1 sq.toCommSq).app
      K₀) := by
    refine isIso_boundedConstructibleBaseChange_integral_app_of_reduction ℓ E.1 _ hsq K₀ ?_
    exact ProEtale.isIso_derivedBaseChangeMap_app_of_smooth _ v.left hsq ℓ
      (Fact.out : ℓ.Prime).ne_zero (ProEtale.natCast_eq_zero_residueFieldCoeff.{u} ℓ E.1) hℓY _
      (ProEtale.boundedConstructible_derivedReduction_obj X.left ℓ E.1 _ K₀.property)
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).1 (by
    simp only [MorphismProperty.isomorphisms.iff]
    infer_instance)

end AlgebraicGeometry.ProEtale.CondensedRing.ContinuousMapRingObj
