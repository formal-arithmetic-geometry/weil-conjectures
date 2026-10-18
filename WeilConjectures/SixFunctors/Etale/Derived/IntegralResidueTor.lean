/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChangeRingEquiv
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsQuotientDerived

/-!
# The residue reduction controls integral Tor amplitude

Let `Λ` be a commutative ring with a maximal ideal `I` (the integral stage `Λ = 𝒪_E`,
`I = 𝔪_E`), and `A_n = Λ ⧸ Iⁿ⁺¹`. For `K ∈ D(X_ét, Λ)` with reductions `K_n = K ⊗ᴸ_Λ A_n`, if
`K_0 = K ⊗ᴸ_Λ Λ ⧸ I` has cohomology in `[a, b]`, then every `K_n` has Tor amplitude in `[a, b]`
over `A_n` (blueprint `lem-coef-integral-residue-tor`).

Following the blueprint, `K_n ⊗ᴸ_{A_n} κ = K_0` by associativity of the coefficient change
(`κ = A_n ⧸ I A_n ≅ Λ ⧸ I`), and the residue test for the local Artinian ring `A_n`
(`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn_of_ideal`,
blueprint `lem-exc-residue-tor-test`) concludes. In the formalisation, associativity is the
composition of derived base changes (`CategoryTheory.Sheaf.IsDerivedBaseChange.comp`) together
with the uniqueness of derived base change and the base change along the isomorphism
`Λ ⧸ I ≅ A_n ⧸ I A_n` (`CategoryTheory.Sheaf.isDerivedBaseChange_ringEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is locally small. Instance search does not find this in the
presence of the imports of this file. -/
local instance (X : Scheme.{u}) : LocallySmall.{u + 1} X.Etale :=
  @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  essentiallySmall_of_small_of_locallySmall _

namespace DerivedCategory

/-- Blueprint `lem-exc-residue-tor-test`, for a nilpotent ideal with semisimple quotient: let
`Λ` be a finite ring and `J` a nilpotent ideal of `Λ` with `Λ ⧸ J` semisimple. Then
`K ∈ D(X_ét, Λ)` has Tor amplitude in `[a, b]` if and only if `K ⊗ᴸ (Λ ⧸ J)_X` has homology
concentrated in `[a, b]`. The case `J` the Jacobson radical is
`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn`. -/
theorem torAmplitudeIn_iff_tensorSingleConcentratedIn_of_ideal {Λ : Type (u + 1)} [CommRing Λ]
    [Finite Λ] (J : Ideal Λ) {m : ℕ} (hm : J ^ m = ⊥) [IsSemisimpleRing (Λ ⧸ J)]
    {X : Scheme.{u}} (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K ↔
      _root_.DerivedCategory.TensorSingleConcentratedIn _ a b K
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Λ ⧸ J))) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  let r : Fin n → Λ := fun i ↦ (e.symm i).1
  have hr : Ideal.span (Set.range r) = J := by
    have : Set.range r = (J : Set Λ) := by
      ext x
      exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ (e.symm i).2, fun hx ↦ ⟨e ⟨x, hx⟩, by simp [r]⟩⟩
    rw [this, Ideal.span_eq]
  rw [← hr] at hm ⊢
  have : IsSemisimpleRing (Λ ⧸ Ideal.span (Set.range r)) := by
    rw [hr]
    infer_instance
  exact _root_.DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn_of_ideal
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (R := Λ) r hm
    (fun x hx ↦ Sheaf.smul_id_constantSheaf_quotient_eq_zero _ _ hx)
    (fun F hF ↦ ⟨Sheaf.constantSheafQuotientTensorIso _ r F hF⟩)
    (fun F _ _ _ f _ _ hY ↦ Sheaf.mono_whiskerRight_of_smul_eq_zero_of_ideal _ f hY F) a b K

end DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [I.IsMaximal] (n : ℕ)
  [Finite (Λ ⧸ I ^ (n + 1))]

/-- Blueprint `lem-coef-integral-residue-tor`: The residue reduction controls integral Tor
amplitude.

Let `I` be a maximal ideal of `Λ` (for the integral stage, `Λ = 𝒪_E` and `I = 𝔪_E`) with
`A_n = Λ ⧸ Iⁿ⁺¹` finite. If the residue reduction `K ⊗ᴸ_Λ Λ ⧸ I` of `K ∈ D(X_ét, Λ)`
(`AlgebraicGeometry.Etale.reductionModIdeal`) has cohomology in `[a, b]`, then every derived
base change `K_n = K ⊗ᴸ_Λ A_n` (`CategoryTheory.Sheaf.IsDerivedBaseChange`) has Tor amplitude
in `[a, b]` over `A_n`. Consequently the derived complete bounded constructible integral objects
have finite Tor amplitude, with one interval for all their reductions: `Dᵇc(X, 𝒪_E) =
Dᵇctf(X, 𝒪_E)`. Neither derived completeness nor constructibility of `K` is needed. -/
theorem torAmplitudeIn_of_isDerivedBaseChange {X : Scheme.{u}} {K : 𝐃(X, Λ)} {a b : ℤ}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b ((reductionModIdeal Λ X I).obj K))
    {Kn : 𝐃(X, Λ ⧸ I ^ (n + 1))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (Ideal.Quotient.mk (I ^ (n + 1)))).obj Kn}
    (hη : Sheaf.IsDerivedBaseChange η) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I ^ (n + 1))) X a b Kn := by
  have hle : I ^ (n + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero n)
  let J' : Ideal (Λ ⧸ I ^ (n + 1)) := I.map (Ideal.Quotient.mk (I ^ (n + 1)))
  let e : Λ ⧸ I ≃+* (Λ ⧸ I ^ (n + 1)) ⧸ J' := (DoubleQuot.quotQuotEquivQuotOfLE hle).symm
  have hJ' : J' ^ (n + 1) = ⊥ := by
    simp only [J', ← Ideal.map_pow, Ideal.map_quotient_self]
  have : IsSemisimpleRing (Λ ⧸ I) := by
    letI := Ideal.Quotient.field I
    infer_instance
  have : IsSemisimpleRing ((Λ ⧸ I ^ (n + 1)) ⧸ J') := e.isSemisimpleRing
  rw [DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn_of_ideal J' hJ',
    tensorSingleConcentratedIn_iff_derivedTensor]
  -- `N` is the derived base change of `K_n` along `A_n ⟶ A_n ⧸ J'`.
  let adj := derivedExtendScalarsAdjunction J' X
  let N := (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J') X).leftDerivedFunctor.obj Kn
  obtain ⟨eN⟩ := nonempty_iso_restrictScalars_leftDerived_obj J' X Kn
  have hu : Sheaf.IsDerivedBaseChange (adj.unit.app Kn) := fun M ↦ by
    convert (adj.homEquiv Kn M).bijective using 1
    ext g
    rw [Adjunction.homEquiv_unit]
  -- `N` is the derived base change of `K` along `Λ ⟶ A_n ⧸ J'`.
  have hψ := hη.comp (gf := (Ideal.Quotient.mk J').comp (Ideal.Quotient.mk (I ^ (n + 1)))) rfl hu
  -- The derived base change `K₀` of `K` along `Λ ⟶ Λ ⧸ I`, which has homology in `[a, b]`.
  let adj₀ := derivedExtendScalarsAdjunction I X
  let K₀ := (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk I) X).leftDerivedFunctor.obj K
  obtain ⟨e₀⟩ := nonempty_iso_restrictScalars_leftDerived_obj I X K
  have hu₀ : Sheaf.IsDerivedBaseChange (adj₀.unit.app K) := fun M ↦ by
    convert (adj₀.homEquiv K M).bijective using 1
    ext g
    rw [Adjunction.homEquiv_unit]
  have hK₀ : _root_.DerivedCategory.homologyConcentratedIn a b K₀ :=
    Sheaf.homologyConcentratedIn_of_derivedRestrictScalars (Ideal.Quotient.mk I)
      ((_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso e₀.symm hK)
  -- Base change along `e` gives another derived base change of `K` along `Λ ⟶ A_n ⧸ J'`.
  have hψ' := hu₀.comp
    (g := e.toRingHom) (gf := (Ideal.Quotient.mk J').comp (Ideal.Quotient.mk (I ^ (n + 1))))
    (RingHom.ext fun _ ↦ rfl) (Sheaf.isDerivedBaseChange_ringEquiv e K₀)
  obtain ⟨eNK⟩ := hψ.nonempty_iso hψ'
  have hN : _root_.DerivedCategory.homologyConcentratedIn a b N :=
    (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso eNK.symm
      ((Sheaf.restrictScalars X.smallEtaleTopology
        e.symm.toRingHom).homologyConcentratedIn_mapDerivedCategory_obj hK₀)
  exact (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso eN
    ((Sheaf.restrictScalars X.smallEtaleTopology
      (Ideal.Quotient.mk J')).homologyConcentratedIn_mapDerivedCategory_obj hN)

/-- Blueprint `lem-coef-integral-residue-tor`: The residue reduction controls integral Tor
amplitude, second half: `Dᵇc(X, 𝒪_E) = Dᵇctf(X, 𝒪_E)`.

If all the reductions `K ⊗ᴸ_Λ Λ ⧸ Iᵐ⁺¹` of `K ∈ D(X_ét, Λ)` have cohomology in one interval
`[a, b]`, which is the boundedness condition of an object of `Dᵇc(X, 𝒪_E)`, then every
derived base change `K_n = K ⊗ᴸ_Λ A_n` has Tor amplitude in the same interval `[a, b]` over
`A_n`: this is the finite Tor amplitude condition defining `Dᵇctf(X, 𝒪_E)`. Only the residue
reduction `m = 0` is used (`AlgebraicGeometry.Etale.torAmplitudeIn_of_isDerivedBaseChange`). -/
theorem torAmplitudeIn_of_isDerivedBaseChange_of_forall {X : Scheme.{u}} {K : 𝐃(X, Λ)}
    {a b : ℤ}
    (hK : ∀ m : ℕ, _root_.DerivedCategory.homologyConcentratedIn a b
      ((reductionModIdeal Λ X (I ^ (m + 1))).obj K))
    {Kn : 𝐃(X, Λ ⧸ I ^ (n + 1))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (Ideal.Quotient.mk (I ^ (n + 1)))).obj Kn}
    (hη : Sheaf.IsDerivedBaseChange η) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I ^ (n + 1))) X a b Kn :=
  torAmplitudeIn_of_isDerivedBaseChange I n (by simpa only [zero_add, pow_one] using hK 0) hη

end Etale

end AlgebraicGeometry
