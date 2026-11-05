/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport
public import WeilConjectures.EtaleCohomology.PoincareDuality.CompactSupportPerfect
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedForget
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar

/-!
# The global sections are perfect at the point

Let `k` be a separably closed field, `X` a separated scheme of finite type over `k` with
structure morphism `a_X : X ⟶ Spec k`, and `K` a bounded constructible complex on `X` of finite
Tor amplitude. This file proves that the ordinary and the compactly supported cohomology
complexes `RΓ(X, K)` and `RΓ_c(X, K)`, and their duals `RHom(-, Λ)`, are *perfect point
complexes* (`DerivedCategory.IsPerfect`), at each coefficient stage of the `ℓ`-adic formalism:
at the finite stages `Λ = A_{E,n}`, at the integral stage `𝒪_E`, at the rational stage `E`
and at `ℚ̄_ℓ` (blueprint `sk-lem-finite`).

## Main statements

At a finite coefficient ring `Λ` whose exponent is invertible on `k`:

- `AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`: `RΓ_c(X, K)` is perfect.
- `AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections`: `RΓ(X, K)` is perfect.
- `AlgebraicGeometry.Etale.isPerfect_ihom_compactlySupportedGlobalSections`,
  `AlgebraicGeometry.Etale.isPerfect_ihom_rightDerivedGlobalSections`: so are their duals.

At the integral stage `𝒪_E`, for a derived complete `K` whose reductions `K ⊗ᴸ 𝒪_E/𝔪_Eⁿ` are
bounded constructible of Tor amplitude in one common interval:

- `AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral`,
  `AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections_integral` and the duals.

At the rational stage `E`, the cohomology of these complexes and of their duals tensored up to
`E`:

- `AlgebraicGeometry.Etale.rationalHomology_globalSections`.

At `ℚ̄_ℓ`, for `k` algebraically closed, `ℓ` different from its characteristic and pro-étale
complexes with constructible `ℓ`-adic cohomology sheaves, in
`WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfectAdic`:

- `AlgebraicGeometry.ProEtale.isPerfect_compactlySupportedGlobalSections_adic`,
  `AlgebraicGeometry.ProEtale.isPerfect_rightDerivedGlobalSections_adic`,
  `AlgebraicGeometry.ProEtale.isPerfect_ihom_compactlySupportedGlobalSections_adic`,
  `AlgebraicGeometry.ProEtale.isPerfect_ihom_rightDerivedGlobalSections_adic`.

## Implementation notes

The finite stage follows the blueprint: `RΓ_c(X, K)` is bounded with finite cohomology and of
finite Tor amplitude (`sk-prop-sf-trace-perfectness`), hence perfect over the Noetherian ring
`Λ` (`DerivedCategory.isPerfect_of_finiteTorAmplitude`). For `RΓ(X, K)` choose a
compactification `X ⟶[j] X̄ ⟶[ā] Spec k` of `a_X`. Then `RΓ(X, K) ≅ RΓ(X̄, Rj_* K)` (Leray) and
`RΓ(X̄, -) ≅ RΓ_c(X̄, -)` since `ā` is proper, and `Rj_* K` is again bounded constructible of
finite Tor amplitude (`sk-thm-sf-direct-image-tor-amplitude`), so the compactly supported case
applies to `Rj_* K` on `X̄`. The integral stage is reduced to its compactly supported case in
the same way.

The rational stage `E = 𝒪_E[1/ℓ]` is the rationalization of the integral stage
(`DerivedCategoryDerivedCompleteRational`), whose objects come from integral ones. There is no
derived category of `E`-modules receiving the rationalized global sections in the repository,
so the rational statements are made on cohomology: `E ⊗_{𝒪_E} Hⁱ(C)` is finite dimensional and
vanishes outside a finite interval, for `C` any of the integral complexes above. By flatness of
`E` over `𝒪_E` these are the cohomology spaces of `C ⊗ᴸ_{𝒪_E} E`, and over a field this is
perfectness (`DerivedCategory.isPerfect_iff`).

At `ℚ̄_ℓ` the coefficients are the pro-étale `ℚ̄_ℓ`-sheaves `WeilCoefficients l` of the Weil
sheaf formalism, and bounded constructible means bounded with cohomology sheaves
`ℓ`-adically constructible (`ProEtale.DerivedCategory.boundedAdicConstructible`),
as in the definition of `AlgebraicGeometry.WeilComplex`. This stage is not deduced from the
integral one (there is no comparison of `ℚ̄_ℓ,X`-modules with `ℓ`-adic towers in the
repository) but proved directly, for `k` algebraically closed as in the blueprint setting
`sk-def-set`: the derived pushforward to `Spec k` of an object of `D^b_c(X, ℚ̄_ℓ)` is in
`D^b_c(Spec k, ℚ̄_ℓ)` by the pro-étale finiteness theorem
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`), and the global sections of such an
object are perfect, the global sections functor on `Spec k` being exact and constructible
sheaves on `Spec k` having finite dimensional global sections.
-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [HasCompactification aX]

include aX in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.
This is also blueprint `thm-pod-point-perfectness` (Point perfectness of global sections), at
the finite stage.

**`RΓ(X, K)` is perfect.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`, the ordinary cohomology
complex `RΓ(X, K)` is a perfect complex of `Λ`-modules. For a compactification
`X ⟶[j] X̄ ⟶[ā] Spec k` of `a_X`, `RΓ(X, K) ≅ RΓ(X̄, Rj_* K) ≅ RΓ_c(X̄, Rj_* K)`, `ā` being
proper, and `Rj_* K ∈ Dctf(X̄, Λ)` (`sk-thm-sf-direct-image-tor-amplitude`). -/
theorem isPerfect_rightDerivedGlobalSections [QuasiCompact aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K).IsPerfect := by
  let c := HasCompactification.compactification aX
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : HasInvertibleExponent Λ c.Z := HasInvertibleExponent.of_hom c.g
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  obtain ⟨hbc, a, b, hta⟩ := hK
  obtain ⟨N, hN0, hNΛ, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := c.Z)
  have : NeZero N := ⟨hN0.ne'⟩
  have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ K
  have : IsNoetherianRing Λ := inferInstance
  have hK' : DerivedCategory.boundedConstructibleFiniteTor Λ c.Z
      ((R((c.i)_*[ModuleCat.{u + 1} Λ])).obj K) :=
    ⟨boundedConstructible_rightDerivedLowerStar_of_finite Λ aX c.g c.i c.comm.symm hbc,
      a, b + 2 * (d : ℤ),
      torAmplitudeIn_rightDerivedLowerStar _ aX c.g c.i c.comm.symm d hd a b N hN hNY hbc hta⟩
  exact (isPerfect_compactlySupportedGlobalSections Λ c.g _ hK').of_iso
    ((compactlySupportedGlobalSectionsIsoOfIsProper _ c.g).app _ ≪≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ c.i).app K)

end Finite

section Integral

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {I}

variable [IsDomain Λ] [IsPrincipalIdealRing Λ] {k : Type u} [Field k] [IsSepClosed k]

variable [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

variable [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [HasCompactification aX]

end Integral

end Etale

namespace ProEtale

section Point

variable (l : ℕ) [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field `K`, the global sections functor on pro-étale sheaves of
`ℚ̄_ℓ`-modules on `Spec K` is exact. -/
instance preservesFiniteColimits_Γ_of_isAlgClosed :
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)) := by
  have h := (Functor.preservesFiniteLimits_tfae
    (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l))).out 3 0
  have h' := (Functor.preservesFiniteColimits_tfae
    (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l))).out 0 3
  exact h'.1 fun S hS ↦ ⟨(h.1 inferInstance S hS).1, by have := hS.epi_g; infer_instance⟩

end Point

end ProEtale

end AlgebraicGeometry
