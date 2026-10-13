/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Ideal.Over
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsQuotientDerived

/-!
# Finite free extensions of finite coefficients

Let `Λ ⟶ Λ'` be a finite free extension of finite coefficient rings, the intended case being
`Λ = 𝒪_E ⧸ ϖ_Eⁿ ⟶ Λ' = 𝒪_L ⧸ ϖ_Eⁿ 𝒪_L = 𝒪_L ⧸ ϖ_L^{en}` for a finite extension `L/E` of
coefficient fields with ramification index `e`. The extension of coefficients
`K ↦ K ⊗_Λ Λ' : D(X_ét, Λ) ⥤ D(X_ét, Λ')` is the derived functor of the exact extension of
scalars of étale sheaves (`AlgebraicGeometry.Etale.derivedExtendScalars`). This file records
(blueprint `lem-coef-finite-free-extension`):

- the coefficient facts: `(ϖ_Eⁿ) 𝒪_L = (ϖ_L^{en})`
  (`Ideal.map_span_singleton_pow_eq_span_singleton_pow_mul`) and `𝒪_L ⧸ ϖ_Eⁿ 𝒪_L` is finite free
  over `𝒪_E ⧸ ϖ_Eⁿ` (`Module.free_quotient_map_of_isPrincipalIdealRing`);
- the five comparisons for finite-Tor constructible complexes: ordinary direct image, closed
  exceptional inverse image, dualizing complex, internal Hom and Verdier dual.

## Implementation notes

As in `WeilConjectures.SixFunctors.Etale.Derived.FiniteCoefficientChange`, the comparisons are
stated as the existence of isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

section Coefficients

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Blueprint `lem-coef-finite-free-extension`: Finite free coefficient extensions and cofinal
levels, the equality of ideals.

If a uniformizer `ϖ_E` of `R = 𝒪_E` becomes `u ϖ_Lᵉ` in `S = 𝒪_L` for a unit `u`, then
`(ϖ_Eⁿ) 𝒪_L = (ϖ_L^{en})` for every `n`; a unit relating the uniformizers does not change the
ideal. -/
theorem Ideal.map_span_singleton_pow_eq_span_singleton_pow_mul {ϖE : R} {ϖL : S} {e : ℕ}
    {v : S} (hv : IsUnit v) (h : algebraMap R S ϖE = v * ϖL ^ e) (n : ℕ) :
    (Ideal.span {ϖE ^ n}).map (algebraMap R S) = Ideal.span {ϖL ^ (e * n)} :=
  sorry

/-- Blueprint `lem-coef-finite-free-extension`: Finite free coefficient extensions and cofinal
levels, the freeness.

If `S = 𝒪_L` is finite and torsion free over the principal ideal domain `R = 𝒪_E`, then for
every ideal `I` of `R` (for instance `I = (ϖ_Eⁿ)`) the quotient `S ⧸ I S` is finite free over
`R ⧸ I`. -/
theorem Module.free_quotient_map_of_isPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R S] [Module.IsTorsionFree R S] (I : Ideal R) :
    Module.Free (R ⧸ I) (S ⧸ I.map (algebraMap R S)) ∧
      Module.Finite (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  sorry

end Coefficients

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ']

/-- Extension of scalars of étale sheaves along a flat ring morphism is exact: it is the
sheafification of the levelwise extension of scalars, which is left exact for flat `Λ'`. -/
instance preservesFiniteLimits_etaleSheafExtendScalars_algebraMap [Module.Flat Λ Λ']
    (X : Scheme.{u}) :
    PreservesFiniteLimits (ProEtale.etaleSheafExtendScalars (algebraMap Λ Λ') X) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat.{u + 1}
    (RingHom.flat_algebraMap_iff.2 inferInstance : (algebraMap Λ Λ').Flat)
  have : PreservesFiniteLimits ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap Λ Λ'))) := by
    constructor
    intro J _ _
    infer_instance
  unfold ProEtale.etaleSheafExtendScalars Sheaf.composeAndSheafify
  have := comp_preservesFiniteLimits
    ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap Λ Λ')))
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  exact comp_preservesFiniteLimits _ _

instance preservesFiniteColimits_etaleSheafExtendScalars {Λ' : Type (u + 1)} [CommRing Λ']
    (φ : Λ →+* Λ') (X : Scheme.{u}) :
    PreservesFiniteColimits (ProEtale.etaleSheafExtendScalars φ X) :=
  have := (ProEtale.etaleSheafExtendScalarsAdjunction φ X).leftAdjoint_preservesColimits
  inferInstance

instance additive_etaleSheafExtendScalars' {Λ' : Type (u + 1)} [CommRing Λ'] (φ : Λ →+* Λ')
    (X : Scheme.{u}) : (ProEtale.etaleSheafExtendScalars φ X).Additive :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ X).left_adjoint_additive

variable (Λ') in
/-- The extension of coefficients `K ↦ K ⊗_Λ Λ' : D(X_ét, Λ) ⥤ D(X_ét, Λ')` along a flat
algebra `Λ'` (for instance a finite free one), the derived functor of the exact extension of
scalars of étale sheaves. -/
noncomputable abbrev derivedExtendScalars [Module.Flat Λ Λ'] (X : Scheme.{u}) :
    𝐃(X, Λ) ⥤ 𝐃(X, Λ') :=
  (ProEtale.etaleSheafExtendScalars (algebraMap Λ Λ') X).leftDerivedFunctor

variable [Module.Free Λ Λ'] [Module.Finite Λ Λ'] [Finite Λ] [Finite Λ'] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))] [HasInvertibleExponent Λ' (Spec (.of k))]

/-- Blueprint `lem-coef-finite-free-extension`: Finite free coefficient extensions, ordinary
direct image.

For a finite free extension `Λ ⟶ Λ'` of finite coefficient rings, a separated morphism of
finite type `f : T ⟶ X` of schemes of finite type over a separably closed field `k` and
`K ∈ Dctf(T, Λ)`, `(Rf_* K) ⊗_Λ Λ' ≅ Rf_*(K ⊗_Λ Λ')`. -/
theorem nonempty_iso_derivedExtendScalars_rightDerivedLowerStar [IsSepClosed k]
    {T X : Scheme.{u}} (aT : T ⟶ Spec (.of k)) (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aT]
    [QuasiCompact aT] [LocallyOfFiniteType aX] [QuasiCompact aX] (f : T ⟶ X) (hf : f ≫ aX = aT)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {K : 𝐃(T, Λ)}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T K) :
    Nonempty ((derivedExtendScalars Λ' X).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ'])).obj ((derivedExtendScalars Λ' T).obj K)) :=
  sorry

/-- Blueprint `lem-coef-finite-free-extension`: Finite free coefficient extensions, closed
exceptional inverse image.

For a finite free extension `Λ ⟶ Λ'` of finite coefficient rings, a closed immersion
`i : Z ⟶ X` of schemes of finite type over an algebraically closed field `k` and
`M ∈ Dctf(X, Λ)`, `(Ri^! M) ⊗_Λ Λ' ≅ Ri^!(M ⊗_Λ Λ')`. -/
theorem nonempty_iso_derivedExtendScalars_rightDerivedUpperShriek [IsAlgClosed k]
    {Z X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i] {M : 𝐃(X, Λ)}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((derivedExtendScalars Λ' Z).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj M) ≅
      (R(i)^![ModuleCat.{u + 1} Λ']).obj ((derivedExtendScalars Λ' X).obj M)) :=
  sorry

/-- Blueprint `lem-coef-finite-free-extension`: Finite free coefficient extensions, the
dualizing complex.

For a finite free extension `Λ ⟶ Λ'` of finite coefficient rings and `X` separated of finite
type over an algebraically closed field `k`, with structure morphism `a`,
`ω_{X,Λ} ⊗_Λ Λ' ≅ ω_{X,Λ'}`. -/
theorem nonempty_iso_derivedExtendScalars_dualizingComplex [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification a] :
    Nonempty ((derivedExtendScalars Λ' X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) a) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ') a) :=
  sorry

/-- Blueprint `lem-coef-finite-free-extension`: Finite free coefficient extensions, internal
Hom.

For a finite free extension `Λ ⟶ Λ'` of finite coefficient rings, `X` separated of finite type
over an algebraically closed field `k` and `K, M ∈ Dctf(X, Λ)`,
`RHom_Λ(K, M) ⊗_Λ Λ' ≅ RHom_{Λ'}(K ⊗_Λ Λ', M ⊗_Λ Λ')`. -/
theorem nonempty_iso_derivedExtendScalars_derivedHom [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    {K M : 𝐃(X, Λ)} (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((derivedExtendScalars Λ' X).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj M) ≅
      ((derivedHom (ModuleCat.{u + 1} Λ') X).obj (op ((derivedExtendScalars Λ' X).obj K))).obj
        ((derivedExtendScalars Λ' X).obj M)) :=
  sorry

/-- Blueprint `lem-coef-finite-free-extension`: Finite free coefficient extensions, Verdier
duality.

For a finite free extension `Λ ⟶ Λ'` of finite coefficient rings, `X` separated of finite type
over an algebraically closed field `k` and `K ∈ Dctf(X, Λ)`,
`(𝔻_{X,Λ} K) ⊗_Λ Λ' ≅ 𝔻_{X,Λ'}(K ⊗_Λ Λ')`. -/
theorem nonempty_iso_derivedExtendScalars_verdierDual [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification a] {K : 𝐃(X, Λ)}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty ((derivedExtendScalars Λ' X).obj ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)) ≅
      (verdierDual (ModuleCat.{u + 1} Λ') a).obj (op ((derivedExtendScalars Λ' X).obj K))) :=
  sorry

end Etale

end AlgebraicGeometry
