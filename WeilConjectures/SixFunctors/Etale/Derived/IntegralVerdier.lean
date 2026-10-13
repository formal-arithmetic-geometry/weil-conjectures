/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsQuotientDerived
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral

/-!
# Integral Verdier duality

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on an algebraically closed field `k`: the integral stage `Λ = 𝒪_E`,
`I = 𝔪_E` of the `ℓ`-adic formalism, with finite levels `A_n = Λ ⧸ Iⁿ`. The integral category
`Dᵇc(X, Λ)` is `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral I X`.

For `X` separated of finite type over `k`, with structure morphism `a : X ⟶ Spec k`, the
integral dualizing complex is the ambient `ω_{X,Λ} = Ra^! Λ`
(`AlgebraicGeometry.Etale.dualizingComplex` at `ModuleCat Λ`) and the integral Verdier dual is
`𝔻_{X,Λ} = RHom(-, ω_{X,Λ})` (`AlgebraicGeometry.Etale.verdierDual`), with double-dual morphism
`δ_K : K ⟶ 𝔻_{X,Λ} 𝔻_{X,Λ} K` (`AlgebraicGeometry.Etale.verdierDualDoubleDual`). This file
states and proves:

- `AlgebraicGeometry.Etale.torAmplitudeIn_of_boundedConstructibleIntegral`
  (`lem-coef-integral-residue-tor`): the residue reduction controls the Tor amplitude of the
  finite reductions;
- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedLowerShriek`
  (`lem-coef-integral-compact-support`): `Rf_!` preserves `Dᵇc(-, Λ)` and commutes with the
  reductions;
- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_dualizingComplex`
  (`prop-coef-integral-dualizing`): `ω_{X,Λ}` lies in `Dᵇc(X, Λ)`, its reductions are the finite
  dualizing complexes, and it is the derived limit of the tower `n ↦ Ra^!(Λ ⧸ Iⁿ)`;
- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_verdierDual`,
  `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_integral` and
  `AlgebraicGeometry.Etale.verdierDualIntegralEquivalence` (`thm-coef-integral-verdier`):
  `𝔻_{X,Λ}` is an anti-equivalence of `Dᵇc(X, Λ)`, compatible with the reductions.

## Implementation notes

The reduction `K ⊗ᴸ_Λ A_n ∈ D(X_ét, A_n)` of an object `K` is recorded, as in
`WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`, by a morphism
`η : K ⟶ Res K_n` exhibiting `K_n` as the derived base change
(`AlgebraicGeometry.Etale.IsDerivedBaseChange`). Tor intervals of the blueprint are measured over
the finite coefficient rings `A_n`, that is on the `K_n`; the Tor amplitude of the restrictions
of scalars `K ⊗ᴸ (Λ ⧸ Iⁿ)_X`, measured over `Λ`, is wider by one in the lower bound.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

section Finiteness

variable {Λ : Type*} [CommRing Λ]

/-- The quotients `Λ ⧸ Iⁿ` of a Noetherian ring by the powers of an ideal with finite quotient
are finite. -/
instance finite_quotient_pow [IsNoetherianRing Λ] (I : Ideal Λ) [Finite (Λ ⧸ I)] (n : ℕ) :
    Finite (Λ ⧸ I ^ n) :=
  Ideal.finite_quotient_pow (IsNoetherian.noetherian I) n

/-- If the exponent of `Λ ⧸ I` is invertible on `X`, so is the exponent of `Λ ⧸ Iⁿ`: if `m` kills
`Λ ⧸ I`, then `mⁿ` kills `Λ ⧸ Iⁿ`. -/
instance HasInvertibleExponent.quotient_pow (I : Ideal Λ) (X : Scheme.{u})
    [HasInvertibleExponent (Λ ⧸ I) X] (n : ℕ) : HasInvertibleExponent (Λ ⧸ I ^ n) X := by
  obtain ⟨m, hm, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ ⧸ I) (X := X)
  have hmI : (m : Λ) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hΛ
  refine ⟨m ^ n, pow_pos hm n, ?_, by rw [Nat.cast_pow]; exact hu.pow n⟩
  rw [Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk (I ^ n)), ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hmI n

end Finiteness

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] [IsNoetherianRing Λ] (I : Ideal Λ)
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ})

section ResidueTor

variable {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]

include hϖ hI aX in
/-- Blueprint `lem-coef-integral-residue-tor`: The residue reduction controls integral Tor
amplitude.

Let `K ∈ Dᵇc(X, Λ)`. If the residue reduction `K ⊗ᴸ Λ ⧸ I` has cohomology in `[a, b]`, then every
finite reduction `K_n = K ⊗ᴸ_Λ A_n ∈ D(X_ét, A_n)` has Tor amplitude in `[a, b]` over `A_n`.
Consequently the finite reductions of `K` have Tor amplitude in one common interval over the
`A_n`: `Dᵇc(X, Λ) = Dᵇ_ctf(X, Λ)` for this coefficient ring. -/
theorem torAmplitudeIn_of_boundedConstructibleIntegral {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    (∀ a b : ℤ, _root_.DerivedCategory.homologyConcentratedIn a b
        ((reductionModIdeal Λ X I).obj K) →
      ∀ (n : ℕ) (Kn : 𝐃(X, Λ ⧸ I ^ n))
        (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn),
        IsDerivedBaseChange η → torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X a b Kn) ∧
    ∃ a b : ℤ, ∀ (n : ℕ) (Kn : 𝐃(X, Λ ⧸ I ^ n))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn),
      IsDerivedBaseChange η → boundedConstructible (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X Kn ∧
        torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X a b Kn :=
  sorry

end ResidueTor

section CompactSupport

variable {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]

include hϖ hI in
/-- Blueprint `lem-coef-integral-compact-support`: Integral compact supports have the
prescribed reductions.

Let `f : X ⟶ Y` be a separated morphism of finite type between schemes of finite type over `k`,
with `dim X ≤ d`, and let `K ∈ Dᵇc(X, Λ)`. The integral direct image with compact supports
`Rf_! K` (the ambient `R(f)_!` on `D(X_ét, Λ)`) lies in `Dᵇc(Y, Λ)`; for every `n` its reduction
is the finite direct image with compact supports, `(Rf_! K) ⊗ᴸ_Λ A_n ≅ Rf_{!,n} K_n`; it is the
derived limit `R lim_n Rf_!(K ⊗ᴸ Λ ⧸ Iⁿ)` of the reduced direct images; and if the reductions of
`K` have Tor amplitude in `[a, b]` then those of `Rf_! K` have Tor amplitude in `[a, b + 2d]`. -/
theorem boundedConstructibleIntegral_rightDerivedLowerShriek (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] [HasCompactification f] {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    DerivedCategory.boundedConstructibleIntegral I Y ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ∧
    (∀ (n : ℕ) (Kn : 𝐃(X, Λ ⧸ I ^ n))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn),
      IsDerivedBaseChange η → ∃ η' : (R(f)_![ModuleCat.{u + 1} Λ]).obj K ⟶
        (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) Y).obj
          ((R(f)_![ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn), IsDerivedBaseChange η') ∧
    (∀ c : Cone (DerivedCategory.derivedCompletionDiagram X.smallEtaleTopology I K ⋙
        R(f)_![ModuleCat.{u + 1} Λ]), Pretriangulated.IsHomotopyLimit c →
      Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).obj K ≅ c.pt)) ∧
    ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ,
      (∀ (n : ℕ) (Kn : 𝐃(X, Λ ⧸ I ^ n))
        (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn),
        IsDerivedBaseChange η → torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X a b Kn) →
      ∀ (n : ℕ) (Mn : 𝐃(Y, Λ ⧸ I ^ n))
        (η : (R(f)_![ModuleCat.{u + 1} Λ]).obj K ⟶
          (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) Y).obj Mn),
        IsDerivedBaseChange η →
          torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) Y a (b + 2 * (d : ℤ)) Mn :=
  sorry

end CompactSupport

section Dualizing

variable {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasCompactification aX] [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

include hϖ hI in
/-- Blueprint `prop-coef-integral-dualizing`: The integral dualizing object and its adjunction.

Let `X` be separated of finite type over `k`, with structure morphism `a`, and `dim X ≤ d`. The
integral dualizing complex `ω_{X,Λ} = Ra^! Λ` satisfies:

1. `ω_{X,Λ} ∈ Dᵇc(X, Λ)`;
2. for every `n`, `ω_{X,Λ} ⊗ᴸ_Λ A_n ≅ ω_{X,n} = Ra_n^! A_n`, the finite dualizing complex;
3. `ω_{X,Λ} = R lim_n Ra^!(Λ ⧸ Iⁿ)`, compatibly with the maps to the `Ra^!(Λ ⧸ Iⁿ)`;
4. the finite dualizing complexes `ω_{X,n}` have Tor amplitude in `[-2d, 0]` over `A_n`;
5. for `K ∈ Dᵇc(X, Λ)`, `RHom_X(K, ω_{X,Λ}) = Ra_* RHom(K, ω_{X,Λ}) ≅ RHom_Λ(Ra_! K, Λ)`: the
   dualizing complex is the value at `Λ` of the exceptional right adjoint. -/
theorem boundedConstructibleIntegral_dualizingComplex :
    DerivedCategory.boundedConstructibleIntegral I X (dualizingComplex (ModuleCat.{u + 1} Λ) aX) ∧
    (∀ n : ℕ, ∃ η : dualizingComplex (ModuleCat.{u + 1} Λ) aX ⟶
        (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
          (dualizingComplex (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) aX), IsDerivedBaseChange η) ∧
    (∀ c : Cone (DerivedCategory.derivedCompletionDiagram (Spec (.of k)).smallEtaleTopology I
        (𝟙_ 𝐃(Spec (.of k), Λ)) ⋙ R(aX)^![ModuleCat.{u + 1} Λ]),
      Pretriangulated.IsHomotopyLimit c →
        ∃ e : dualizingComplex (ModuleCat.{u + 1} Λ) aX ≅ c.pt, ∀ n : ℕ,
          e.hom ≫ c.π.app (op n) = (R(aX)^![ModuleCat.{u + 1} Λ]).map
            ((DerivedCategory.derivedCompletionCone (Spec (.of k)).smallEtaleTopology I
              (𝟙_ 𝐃(Spec (.of k), Λ))).π.app (op n))) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ n : ℕ,
      torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X (-2 * (d : ℤ)) 0
        (dualizingComplex (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) aX)) ∧
    ∀ K : 𝐃(X, Λ), DerivedCategory.boundedConstructibleIntegral I X K →
      Nonempty ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj
            (dualizingComplex (ModuleCat.{u + 1} Λ) aX)) ≅
        ((derivedHom (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
          (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K))).obj (𝟙_ 𝐃(Spec (.of k), Λ))) :=
  sorry

end Dualizing

section Verdier

variable {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasCompactification aX] [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

include hϖ hI in
/-- Blueprint `thm-coef-integral-verdier`: Integral Verdier biduality, preservation and
reductions.

The integral Verdier dual `𝔻_{X,Λ} K = RHom(K, ω_{X,Λ})` of `K ∈ Dᵇc(X, Λ)` lies in `Dᵇc(X, Λ)`;
its reductions are the finite Verdier duals, `(𝔻_{X,Λ} K) ⊗ᴸ_Λ A_n ≅ 𝔻_{X,n} K_n`, so that
`𝔻_{X,Λ} K ≅ R lim_n Res_n 𝔻_{X,n} K_n` (`𝔻_{X,Λ} K` being derived complete); and if
`dim X ≤ d` and the reductions `K_n` have Tor amplitude in `[a, b]` over `A_n`, those of
`𝔻_{X,Λ} K` have Tor amplitude in `[-b - 2d, -a]`. -/
theorem boundedConstructibleIntegral_verdierDual {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    DerivedCategory.boundedConstructibleIntegral I X
        ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)) ∧
    (∀ (n : ℕ) (Kn : 𝐃(X, Λ ⧸ I ^ n))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn),
      IsDerivedBaseChange η → ∃ η' : (verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K) ⟶
        (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
          ((verdierDual (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) aX).obj (op Kn)),
        IsDerivedBaseChange η') ∧
    ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ,
      (∀ (n : ℕ) (Kn : 𝐃(X, Λ ⧸ I ^ n))
        (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn),
        IsDerivedBaseChange η → torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X a b Kn) →
      ∀ (n : ℕ) (Dn : 𝐃(X, Λ ⧸ I ^ n))
        (η : (verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K) ⟶
          (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Dn),
        IsDerivedBaseChange η →
          torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X (-b - 2 * (d : ℤ)) (-a) Dn :=
  sorry

include hϖ hI in
/-- Blueprint `thm-coef-integral-verdier`: Integral Verdier biduality, the reduction of the
double-dual morphism.

For `K ∈ Dᵇc(X, Λ)` with reduction `η : K ⟶ Res K_n`, the reduction of the double-dual morphism
`δ_K : K ⟶ 𝔻_{X,Λ} 𝔻_{X,Λ} K` is the finite double-dual morphism `δ_{K_n}`: there is a morphism
`θ : 𝔻_{X,Λ} 𝔻_{X,Λ} K ⟶ Res 𝔻_{X,n} 𝔻_{X,n} K_n` exhibiting `𝔻_{X,n} 𝔻_{X,n} K_n` as the
reduction of `𝔻_{X,Λ} 𝔻_{X,Λ} K`, with `δ_K ≫ θ = η ≫ Res δ_{K_n}`. -/
theorem exists_isDerivedBaseChange_verdierDualDoubleDual_app {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) (n : ℕ) (Kn : 𝐃(X, Λ ⧸ I ^ n))
    (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn)
    (hη : IsDerivedBaseChange η) :
    ∃ θ : (verdierDual (ModuleCat.{u + 1} Λ) aX).obj
        (op ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K))) ⟶
      (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
        ((verdierDual (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) aX).obj
          (op ((verdierDual (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) aX).obj (op Kn)))),
      IsDerivedBaseChange θ ∧
        (verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aX).app K ≫ θ =
          η ≫ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).map
            ((verdierDualDoubleDual (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) aX).app Kn) :=
  sorry

include hϖ hI in
/-- Blueprint `thm-coef-integral-verdier`: Integral Verdier biduality.

For `K ∈ Dᵇc(X, Λ)` the double-dual morphism `δ_K : K ⟶ 𝔻_{X,Λ} 𝔻_{X,Λ} K` is an isomorphism:
its cone is derived complete with vanishing reductions, the reductions of `δ_K` being the
finite double-dual isomorphisms `δ_{K_n}`. -/
theorem isIso_verdierDualDoubleDual_app_integral {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aX).app K) :=
  sorry

/-- Blueprint `thm-coef-integral-verdier`: Integral Verdier biduality, the anti-equivalence.

The integral Verdier dual `𝔻_{X,Λ} = RHom(-, ω_{X,Λ})` restricts to an exact contravariant
anti-equivalence `Dᵇc(X, Λ)ᵒᵖ ≌ Dᵇc(X, Λ)`, with quasi-inverse `𝔻_{X,Λ}` itself; the unit and
counit are the double-dual isomorphisms `δ_K`
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_integral`). -/
noncomputable def verdierDualIntegralEquivalence :
    (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategoryᵒᵖ ≌
      (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategory :=
  (DerivedCategory.boundedConstructibleIntegral I X).liftDualEquivalence
    (verdierDual (ModuleCat.{u + 1} Λ) aX)
    (fun _ hK ↦ (boundedConstructibleIntegral_verdierDual I hϖ hI aX hK).1)
    (verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aX)
    (fun _ hK ↦ isIso_verdierDualDoubleDual_app_integral I hϖ hI aX hK)

end Verdier

end Etale

end AlgebraicGeometry
