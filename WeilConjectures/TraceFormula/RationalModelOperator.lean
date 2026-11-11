/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriek
public import WeilConjectures.TraceFormula.RationalModel

/-!
# The operators of rational Frobenius correspondences and of their integral models

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. For a proper
endomorphism `Φ` of `X` and a Frobenius correspondence `ψ : LΦ^* K ⟶ K` with coefficients `E`
(resp. `𝒪_E`), the operator `T_{c_m}(ψ_m) = RΓ_c(X, ψ_m) ∘ Φ_m^♯` on `RΓ_c(X, K)` is defined as
for `ℚ̄_ℓ` (`ProEtale.CondensedRing.frobeniusCompactOperator`), with the pullback `Φ_m^♯` on
compactly supported cohomology induced by the unit of `LΦ_m^* ⊣ RΦ_{m*}` and `RΦ_{m!} ≅ RΦ_{m*}`
(`ProEtale.CondensedRing.ContinuousMapRingObj.compactPullback`,
`ProEtale.CondensedRing.PadicIntegersRingObj.compactPullback`).

For an integral model `(K₀, θ)` of `(K, ψ)` with `ℓ^N ψ = θ ⊗ E`
(`ProEtale.CondensedRing.exists_integralModel_frobeniusCorrespondence`), the operators satisfy
`ℓ^{N m} T_{c_m}(ψ_m) = T_{c_m}(θ_m) ⊗ E`
(`ProEtale.CondensedRing.pow_smul_frobeniusCompactOperator_eq`, blueprint
`lemma-integral-models-rational-frobenius-correspondences--2`, stated with `sorry`). As in
`WeilConjectures.TraceFormula.RationalModel`, the denominator is a power of `ℓ` rather than of
`π_E`, which is equivalent.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory MonObj

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : FiniteIntermediateField ℓ)
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

-- The coefficient ring `𝒪_E`.
set_option quotPrecheck false in
local notation "𝒪" => Profinite.padicIntegersRingObj ℓ E.1

-- The coefficient ring `E`.
set_option quotPrecheck false in
local notation "𝔼" => Profinite.continuousMapRingObj E.1

variable {K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X.left)}
  {K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)}

namespace ContinuousMapRingObj

/-- The isomorphism `Rh_! ≅ Rh_*` on bounded constructible `E`-sheaves for a proper `h`. -/
noncomputable def boundedConstructibleLowerShriekIsoLowerStar (h : Y ⟶ X) [IsProper h.left] :
    boundedConstructibleLowerShriek ℓ E h ≅ boundedConstructibleLowerStar ℓ E h :=
  boundedConstructibleLowerShriekOfCompactificationIso ℓ E (compactificationOverField h)
      (.ofIsProper h.left) ≪≫
    (Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso 𝔼 ℓ h) _ ≪≫
      Functor.leftUnitor _)

/-- The *pullback on compactly supported cohomology* `h^♯ : RΓ_c(X, -) ⟶ RΓ_c(Y, Lh^* -)`
along a proper morphism `h : Y ⟶ X`, for `E`-coefficients: the composite
```
Ra_{X!} K ⟶ Ra_{X!} Rh_* Lh^* K ≅ Ra_{X!} Rh_! Lh^* K ≅ R(h ≫ a_X)_! Lh^* K = Ra_{Y!} Lh^* K.
```
-/
noncomputable def compactPullback (h : Y ⟶ X) [IsProper h.left] :
    boundedConstructibleLowerShriek ℓ E (toPoint X) ⟶
      boundedConstructibleUpperStar 𝔼 ℓ h ⋙ boundedConstructibleLowerShriek ℓ E (toPoint Y) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E h).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar ℓ E h).inv _) ≫
    Functor.whiskerLeft _ ((boundedConstructibleLowerShriekComp ℓ E h (toPoint X)).inv ≫
      eqToHom (by rw [comp_toPoint]))

variable {ℓ E}

/-- The global operator `T_{c_m}(ψ_m) = RΓ_c(X, ψ_m) ∘ Φ_m^♯` on `RΓ_c(X, K)` of a Frobenius
correspondence `ψ : LΦ^* K ⟶ K` with `E`-coefficients (blueprint
`definition-frobenius-correspondences-their-operators`). -/
noncomputable def frobeniusCompactOperator {Φ : X ⟶ X} [IsProper Φ.left]
    (ψ : (boundedConstructibleUpperStar 𝔼 ℓ Φ).obj K ⟶ K) (m : ℕ) :
    (boundedConstructibleLowerShriek ℓ E (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek ℓ E (toPoint X)).obj K :=
  (compactPullback ℓ E (frobeniusIterate Φ m)).app K ≫
    (boundedConstructibleLowerShriek ℓ E (toPoint X)).map (frobeniusCoefficientIterate ψ m)

end ContinuousMapRingObj

namespace PadicIntegersRingObj

/-- The *pullback on compactly supported cohomology* `h^♯ : RΓ_c(X, -) ⟶ RΓ_c(Y, Lh^* -)`
along a proper morphism `h : Y ⟶ X`, for `𝒪_E`-coefficients. -/
noncomputable def compactPullback (h : Y ⟶ X) [IsProper h.left] :
    boundedConstructibleLowerShriek ℓ E.1 (toPoint X) ⟶
      boundedConstructibleUpperStar 𝒪 ℓ h ⋙ boundedConstructibleLowerShriek ℓ E.1 (toPoint Y) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E.1 h).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E.1 h).inv _) ≫
    Functor.whiskerLeft _ ((boundedConstructibleLowerShriekComp_padicIntegers ℓ E.1 h
      (toPoint X)).inv ≫ eqToHom (by rw [comp_toPoint]))

variable {ℓ E}

/-- The global operator `T_{c_m}(θ_m) = RΓ_c(X, θ_m) ∘ Φ_m^♯` on `RΓ_c(X, K₀)` of a Frobenius
correspondence `θ : LΦ^* K₀ ⟶ K₀` with `𝒪_E`-coefficients (blueprint
`definition-frobenius-correspondences-their-operators`). -/
noncomputable def frobeniusCompactOperator {Φ : X ⟶ X} [IsProper Φ.left]
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K₀ ⟶ K₀) (m : ℕ) :
    (boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).obj K₀ ⟶
      (boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).obj K₀ :=
  (compactPullback ℓ E (frobeniusIterate Φ m)).app K₀ ≫
    (boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).map (frobeniusCoefficientIterate θ m)

end PadicIntegersRingObj

/-- Blueprint `lemma-integral-models-rational-frobenius-correspondences--2`: if `ℓ^N ψ = θ ⊗ E`
for a Frobenius correspondence `ψ : LΦ^* K ⟶ K` with `E`-coefficients and an integral model
`θ : LΦ^* K₀ ⟶ K₀`, read through `e : (K₀)_E ≅ K` and the canonical comparison
`LΦ^* ⋙ (-)_E ≅ (-)_E ⋙ LΦ^*` (as produced by `exists_integralModel_frobeniusCorrespondence`),
then for every `m` the operators of the iterates satisfy
```
ℓ^{N m} T_{c_m}(ψ_m) = T_{c_m}(θ_m) ⊗ E,
```
read through `RΓ_c(X, e)` and the compatibility `RΓ_c(X, -) ⋙ (-)_E ≅ (-)_E ⋙ RΓ_c(X, -)`
(`boundedConstructibleLowerShriekExtendScalarsIso`). -/
theorem pow_smul_frobeniusCompactOperator_eq {Φ : X ⟶ X} [IsProper Φ.left]
    (e : (boundedConstructibleExtendScalars X.left ℓ E).obj K₀ ≅ K) {N : ℕ}
    {ψ : (boundedConstructibleUpperStar 𝔼 ℓ Φ).obj K ⟶ K}
    {θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K₀ ⟶ K₀}
    (h : ((ℓ : ℤ) ^ N) • ψ =
      (boundedConstructibleUpperStar 𝔼 ℓ Φ).map e.inv ≫
        (boundedConstructibleUpperStarExtendScalarsIso ℓ E Φ).inv.app K₀ ≫
        (boundedConstructibleExtendScalars X.left ℓ E).map θ ≫ e.hom)
    (m : ℕ) :
    ((ℓ : ℤ) ^ (N * m)) • ContinuousMapRingObj.frobeniusCompactOperator (E := E) ψ m =
      (ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E (toPoint X)).map e.inv ≫
        (boundedConstructibleLowerShriekExtendScalarsIso ℓ E (toPoint X)).inv.app K₀ ≫
        (boundedConstructibleExtendScalars _ ℓ E).map
          (PadicIntegersRingObj.frobeniusCompactOperator (E := E) θ m) ≫
        (boundedConstructibleLowerShriekExtendScalarsIso ℓ E (toPoint X)).hom.app K₀ ≫
        (ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E (toPoint X)).map e.hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
