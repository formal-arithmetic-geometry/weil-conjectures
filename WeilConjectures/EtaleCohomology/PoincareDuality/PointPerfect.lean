/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsComplete
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedForget
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek

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

- `AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral` and its dual,
  assuming moreover that `RΓ_c(X, K)` is derived complete (automatic for proper `X`);
- `AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections_integral` and its dual.

At the rational stage `E`, the cohomology of these complexes and of their duals tensored up to
`E`:

- `AlgebraicGeometry.Etale.rationalHomology_globalSections`.

At `ℚ̄_ℓ`, for `k` algebraically closed, `ℓ` different from its characteristic and pro-étale
complexes with constructible `ℓ`-adic cohomology sheaves:

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

At the integral stage, `RΓ_c(X, K) ⟶ϖ RΓ_c(X, K) ⟶ RΓ_c(X, K ⊗ᴸ 𝒪_E/ϖ)` is a distinguished
triangle with perfect third vertex, and a derived complete complex with perfect reduction is
perfect (Stacks 0CQG, `DerivedCategory.isPerfect_of_rightOrthogonal_of_isPerfect_obj₃`). The
blueprint's integral `RΓ_c(X, K)` is the derived limit of the `RΓ_c(X, K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)`, which
is derived complete; the naive `RΓ_c(X, K) = RΓ(X̄, j_! K)` of the repository need not be, as
`j_!` does not commute with derived limits, whence the completeness hypothesis. For `RΓ(X, K)`
it holds automatically: `RΓ(X, K) = RΓ(X̄, Rj_* K)` and `Rj_*` preserves derived completeness.

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

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [HasCompactification aX]

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ_c(X, K)` is perfect.** Let `Λ` be a finite ring whose exponent is invertible in the
separably closed field `k`, `X` separated of finite type over `k` and `K ∈ Dctf(X, Λ)`. Then
`RΓ_c(X, K)` is a perfect complex of `Λ`-modules: it is bounded with finite cohomology modules
and of finite Tor amplitude (`sk-prop-sf-trace-perfectness`), hence perfect over the
Noetherian ring `Λ`. -/
theorem isPerfect_compactlySupportedGlobalSections
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect := by
  have := HasInvertibleExponent.of_hom (Λ := Λ) aX
  obtain ⟨a, b, hab⟩ := isZero_compactlySupportedCohomology_of_lt Λ aX K hK
  refine _root_.DerivedCategory.isPerfect_of_finiteTorAmplitude ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
    (finite_compactlySupportedCohomology Λ aX K hK)
    (finiteTorAmplitude_compactlySupportedGlobalSections Λ aX K hK)
  · change _root_.DerivedCategory.IsGE _ a
    rw [_root_.DerivedCategory.isGE_iff]
    exact fun q hq ↦ hab q (Or.inl hq)
  · change _root_.DerivedCategory.IsLE _ b
    rw [_root_.DerivedCategory.isLE_iff]
    exact fun q hq ↦ hab q (Or.inr hq)

include aX in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

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
    ⟨boundedConstructible_rightDerivedLowerStar _ aX c.g c.i c.comm.symm N hN hNY hbc,
      a, b + 2 * (d : ℤ),
      torAmplitudeIn_rightDerivedLowerStar _ aX c.g c.i c.comm.symm d hd a b N hN hNY hbc hta⟩
  exact (isPerfect_compactlySupportedGlobalSections Λ c.g _ hK').of_iso
    ((compactlySupportedGlobalSectionsIsoOfIsProper _ c.g).app _ ≪≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ c.i).app K)

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**The dual of `RΓ_c(X, K)` is perfect.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`, the dual
`RHom_Λ(RΓ_c(X, K), Λ)` is a perfect complex of `Λ`-modules. -/
theorem isPerfect_ihom_compactlySupportedGlobalSections
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_compactlySupportedGlobalSections Λ aX K hK).ihom_unit

include aX in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**The dual of `RΓ(X, K)` is perfect.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`, the dual
`RHom_Λ(RΓ(X, K), Λ)` is a perfect complex of `Λ`-modules. -/
theorem isPerfect_ihom_rightDerivedGlobalSections [QuasiCompact aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_rightDerivedGlobalSections Λ aX K hK).ihom_unit

end Finite

section Integral

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- The integral stage `D^b_c(X, Λ)` of the `ℓ`-adic formalism, for `Λ = 𝒪_E` and `I = 𝔪_E`, as
an object property of `D(X_ét, Λ)`: the objects `K` which are derived complete for `I` and whose
reductions `K ⊗ᴸ Λ/Iⁿ⁺¹` are bounded constructible of Tor amplitude in one common interval
`[a, b]`. -/
def DerivedCategory.boundedConstructibleIntegral (X : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ DerivedCategory.derivedComplete X.smallEtaleTopology I K ∧
    ∃ a b : ℤ, ∀ n : ℕ,
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)

variable [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [HasCompactification aX]

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ_c(X, K)` is perfect at the integral stage.** Let `Λ` be a Noetherian domain, complete for
a principal ideal `I` with `Λ/I` finite of exponent invertible in `k`; this is the integral
stage `Λ = 𝒪_E`, `I = 𝔪_E` for `E` finite over `ℚ_ℓ`. For `K ∈ D^b_c(X, Λ)` such that
`Ra_{X!} K` is derived complete for `I`, the compactly supported cohomology `RΓ_c(X, K)` is a
perfect complex of `Λ`-modules.

The completeness hypothesis says that `RΓ_c(X, K)` is the integral stage of the blueprint: the
derived limit of its reductions `RΓ_c(X, K ⊗ᴸ Λ/Iⁿ)` (the uniform-tower reconstruction
`lem-weil-pbc-reconstruction-uniform-tower`). It holds when `a_X` is proper
(`AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerShriek`), but not in general: the
naive `Ra_{X!} = Rā_* j_!` of the repository does not commute with derived limits, and without
the hypothesis the statement is false (for `X = 𝔸¹` and `K = R lim_n (ℤ/ℓⁿ)_X`, `H²_c(X, K)` is
not finitely generated).

For `I = (ϖ)` with `ϖ ≠ 0` there is a distinguished triangle
`RΓ_c(X, K) ──ϖ──▶ RΓ_c(X, K) ⟶ RΓ_c(X, K ⊗ᴸ Λ/ϖ) ⟶ RΓ_c(X, K)⟦1⟧`, whose third vertex is
perfect by the finite stage
(`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_of_nsmul_eq_zero`), and
`RΓ_c(X, K) = RΓ(Spec k, Ra_{X!} K)` is derived `ϖ`-complete; such a complex is perfect
(Stacks 0CQG, `DerivedCategory.isPerfect_of_rightOrthogonal_of_isPerfect_obj₃`). For `I = 0`
one has `K ≅ K ⊗ᴸ Λ/I`, and the finite stage applies directly. -/
theorem isPerfect_compactlySupportedGlobalSections_integral (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K)
    (hc : _root_.DerivedCategory.derivedComplete (Spec (.of k)).smallEtaleTopology I
      ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect := by
  obtain ⟨-, a, b, hab⟩ := hK
  obtain ⟨m, hm0, hmΛ, hmk⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ ⧸ I)
    (X := Spec (.of k))
  have : NeZero m := ⟨hm0.ne'⟩
  have hmI : (m : Λ) ∈ I ^ 1 := by
    rw [pow_one, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hmΛ
  -- the finite stage: `RΓ_c(X, K ⊗ᴸ Λ/I)` is perfect
  have h₁ : ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj
      ((reductionModIdeal Λ X (I ^ 1)).obj K)).IsPerfect :=
    isPerfect_compactlySupportedGlobalSections_of_nsmul_eq_zero Λ aX _ m
      (nsmul_id_reductionModIdeal hmI K) hmk ⟨(hab 0).1, a, b, (hab 0).2⟩
  obtain ⟨ϖ, rfl⟩ := hI.principal
  by_cases h0 : ϖ = 0
  · -- `I = 0`: `K ≅ K ⊗ᴸ Λ/I`
    subst h0
    refine h₁.of_iso ((compactlySupportedGlobalSections _ aX).mapIso
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
            (Submodule.quotEquivOfEqBot _ ?_).toModuleIso)) ≪≫ derivedTensorSingleUnitIso K))
    rw [pow_one, Submodule.span_singleton_eq_bot]
  have hϖ : ϖ ∈ nonZeroDivisors Λ := mem_nonZeroDivisors_of_ne_zero h0
  obtain ⟨g, h, hT⟩ := exists_distinguished_smul_map_reductionModIdeal
    (R(aX)_![ModuleCat.{u + 1} Λ] ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
      (Spec (.of k))) hϖ 1 K
  rw [pow_one] at hT
  exact _root_.DerivedCategory.isPerfect_of_rightOrthogonal_of_isPerfect_obj₃ hϖ
    (IsAdicComplete.le_jacobson_bot _ (Submodule.mem_span_singleton_self ϖ)) hT
    (rightDerivedGlobalSections_hom_eq_zero
      ((_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ rfl).1 hc)) h₁

omit [IsSeparated aX] in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ(X, K)` is perfect at the integral stage.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral`, the cohomology
`RΓ(X, K)` is a perfect complex of `Λ`-modules. As at the finite stage, for a compactification
`X ⟶[j] X̄ ⟶[ā] Spec k` of `a_X` one has `RΓ(X, K) ≅ RΓ_c(X̄, Rj_* K)`, and
`Rj_* K ∈ D^b_c(X̄, Λ)`: `Rj_*` preserves derived completeness, commutes with the reductions,
and carries Tor amplitude `[a, b]` to `[a, b + 2 dim X]`. No completeness hypothesis on
`RΓ(X, K)` is needed: `ā` being proper, `Rā_! Rj_* K ≅ Rā_* Rj_* K` is derived complete
(`AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerShriek`). -/
theorem isPerfect_rightDerivedGlobalSections_integral [QuasiCompact aX] (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K).IsPerfect := by
  let c := HasCompactification.compactification aX
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  obtain ⟨hc, a, b, hab⟩ := hK
  have hK' : DerivedCategory.boundedConstructibleIntegral I c.Z
      ((R((c.i)_*[ModuleCat.{u + 1} Λ])).obj K) := by
    refine ⟨derivedComplete_rightDerivedLowerStar I hI c.i K hc, a, b + 2 * (d : ℤ),
      fun n ↦ ?_⟩
    obtain ⟨x, hx⟩ := hI.principal
    have hJ : (I ^ (n + 1)).IsPrincipal :=
      ⟨⟨x ^ (n + 1), by rw [hx, Ideal.submodule_span_eq, Ideal.span_singleton_pow]⟩⟩
    obtain ⟨e⟩ := nonempty_iso_reductionModIdeal_rightDerivedLowerStar Λ c.i _ hJ
    obtain ⟨hbc, hta⟩ := hab n
    -- the reduction is killed by `N = mⁿ⁺¹`, for `m` the exponent of `Λ/I`
    have : HasInvertibleExponent (Λ ⧸ I) c.Z := HasInvertibleExponent.of_hom c.g
    obtain ⟨m, hm0, hmΛ, hmY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ ⧸ I)
      (X := c.Z)
    have hmI : (m : Λ) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact hmΛ
    have : NeZero (m ^ (n + 1)) := ⟨pow_ne_zero _ hm0.ne'⟩
    have hNY : IsUnit ((m ^ (n + 1) : ℕ) : Γ(c.Z, ⊤)) := by
      rw [Nat.cast_pow]; exact hmY.pow _
    have hN := nsmul_id_reductionModIdeal (J := I ^ (n + 1)) (N := m ^ (n + 1))
      (by rw [Nat.cast_pow]; exact Ideal.pow_mem_pow hmI _) K
    exact ⟨(DerivedCategory.boundedConstructible _ _).prop_of_iso (e.app K).symm
        (boundedConstructible_rightDerivedLowerStar _ aX c.g c.i c.comm.symm _ hN hNY hbc),
      (DerivedCategory.torAmplitudeIn _ _ _ _).prop_of_iso (e.app K).symm
        (torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing _ aX c.g c.i c.comm.symm d hd a b
          _ hN hNY hbc hta)⟩
  have : IsProper c.g := c.isProper
  exact (isPerfect_compactlySupportedGlobalSections_integral I c.g hI _ hK'
    (derivedComplete_rightDerivedLowerShriek I hI c.g _
      (derivedComplete_rightDerivedLowerStar I hI c.i K hc))).of_iso
    ((compactlySupportedGlobalSectionsIsoOfIsProper _ c.g).app _ ≪≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ c.i).app K)

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**The dual of `RΓ_c(X, K)` is perfect at the integral stage.** -/
theorem isPerfect_ihom_compactlySupportedGlobalSections_integral (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K)
    (hc : _root_.DerivedCategory.derivedComplete (Spec (.of k)).smallEtaleTopology I
      ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)) :
    ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_compactlySupportedGlobalSections_integral I aX hI K hK hc).ihom_unit

omit [IsSeparated aX] in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**The dual of `RΓ(X, K)` is perfect at the integral stage.** -/
theorem isPerfect_ihom_rightDerivedGlobalSections_integral [QuasiCompact aX]
    (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_rightDerivedGlobalSections_integral I aX hI K hK).ihom_unit

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**The rational stage.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral`, let `E` be a
field which is a `Λ`-algebra (for `Λ = 𝒪_E` the fraction field `E`, so that `K ⊗ E` is an
object of the rational stage `D^b_c(X, E)`). The spaces `E ⊗_Λ Hⁱ_c(X, K)` and
`E ⊗_Λ Hⁱ(X, K)`, as well as those of the duals of `RΓ_c(X, K)` and `RΓ(X, K)`, are finite
dimensional and vanish outside a finite interval: the rationalized complexes are perfect
complexes of `E`-vector spaces. This is flat extension of scalars from the integral stage. -/
theorem rationalHomology_globalSections [QuasiCompact aX] (hI : I.IsPrincipal)
    (E : Type*) [Field E] [Algebra Λ E]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K)
    (hc : _root_.DerivedCategory.derivedComplete (Spec (.of k)).smallEtaleTopology I
      ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)) :
    ∀ C ∈ ({(compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K,
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K,
        (ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K)).obj (𝟙_ _),
        (ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj (𝟙_ _)} :
          Set (_root_.DerivedCategory (ModuleCat.{u + 1} Λ))),
      (∀ i, FiniteDimensional E
        (E ⊗[Λ] (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj C)) ∧
      ∃ a b : ℤ, ∀ i, i < a ∨ b < i →
        Subsingleton
          (E ⊗[Λ] (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj C) := by
  intro C hC
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · exact (isPerfect_compactlySupportedGlobalSections_integral I aX hI K hK hc).tensor_homology
      E
  · exact (isPerfect_rightDerivedGlobalSections_integral I aX hI K hK).tensor_homology E
  · exact
      (isPerfect_ihom_compactlySupportedGlobalSections_integral I aX hI K hK hc).tensor_homology
      E
  · exact (isPerfect_ihom_rightDerivedGlobalSections_integral I aX hI K hK).tensor_homology E

end Integral

end Etale

/-- A module over `ULift ℚ̄_ℓ` whose underlying `ℚ̄_ℓ`-vector space is finite dimensional is a
finite module. -/
lemma WeilCoefficients.finite_of_finiteDimensional (l : ℕ) [Fact l.Prime]
    (M : WeilCoefficients.{u} l) [h : FiniteDimensional (PadicAlgCl l) ((toModuleCat l).obj M)] :
    Module.Finite (ULift.{u + 1} (PadicAlgCl l)) M := by
  obtain ⟨s, hs⟩ := h.fg_top
  refine ⟨⟨s, eq_top_iff.2 ?_⟩⟩
  rintro x -
  have hx : x ∈ Submodule.span (PadicAlgCl l) (s : Set ((toModuleCat l).obj M)) := hs ▸ trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
  | smul c y _ hy => exact Submodule.smul_mem _ (ULift.up c) hy

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

/-- Over an algebraically closed field `K`: for `M ∈ D^b_c(Spec K, ℚ̄_ℓ)` the derived global
sections of the underlying complex of sheaves of `ℚ̄_ℓ`-modules form a perfect complex. The
global sections functor is exact, so `Hⁿ(RΓ(Spec K, M)) = Γ(Spec K, Hⁿ(M))`, which vanishes
outside the amplitude of `M` and is finite dimensional, `Hⁿ(M)` being constructible
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.finiteDimensional_globalSections`). -/
theorem isPerfect_rightDerivedGlobalSections_forget_of_isAlgClosed
    (M : _root_.DerivedCategory (AdicSheaf l (Spec (.of K))))
    (hM : DerivedCategory.boundedAdicConstructible l _ M) :
    ((rightDerivedGlobalSections (WeilCoefficients.{u} l) (Spec (.of K))).obj
      ((AdicSheaf.forget _).mapDerivedCategory.obj M)).IsPerfect := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hM
  have e (n : ℤ) : (_root_.DerivedCategory.homologyFunctor _ n).obj
      ((rightDerivedGlobalSections (WeilCoefficients.{u} l) (Spec (.of K))).obj
        ((AdicSheaf.forget _).mapDerivedCategory.obj M)) ≅
      (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj
        ((_root_.DerivedCategory.homologyFunctor _ n).obj M).X :=
    (Functor.rightDerivedFunctorHomologyFunctorIso _ n).symm.app _ ≪≫
      (Sheaf.Γ _ _).mapIso
        (((AdicSheaf.forget _).mapDerivedCategoryHomologyFunctorIso n).app M).symm
  rw [_root_.DerivedCategory.isPerfect_iff]
  refine ⟨⟨a, b, ?_, ?_⟩, fun n ↦ ?_⟩
  · rw [_root_.DerivedCategory.isGE_iff]
    intro n hn
    exact (Functor.map_isZero _ (Functor.map_isZero (AdicSheaf.forget _)
      ((_root_.DerivedCategory.isGE_iff M a).1 ha n hn))).of_iso (e n)
  · rw [_root_.DerivedCategory.isLE_iff]
    intro n hn
    exact (Functor.map_isZero _ (Functor.map_isZero (AdicSheaf.forget _)
      ((_root_.DerivedCategory.isLE_iff M b).1 hb n hn))).of_iso (e n)
  · have := IsAdicConstructibleSheaf.finiteDimensional_globalSections (hc n)
    have := WeilCoefficients.finite_of_finiteDimensional l
      ((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj
        ((_root_.DerivedCategory.homologyFunctor _ n).obj M).X)
    exact Module.Finite.equiv (e n).toLinearEquiv.symm

end Point

section Adic

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [IsAlgClosed k] [Fact (ringChar k ≠ l)]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [HasCompactification aX]

omit [IsSeparated aX] [LocallyOfFiniteType aX] in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ_c(X, K)` is perfect at `ℚ̄_ℓ`.** Let `ℓ` be different from the characteristic of the
algebraically closed field `k`. For `K ∈ D^b_c(X, ℚ̄_ℓ)`, the compactly supported cohomology
`RΓ_c(X, K)` is a perfect complex of `ℚ̄_ℓ`-vector spaces: bounded with finite dimensional
cohomology. For the compactification `X ⟶[j] X̄ ⟶[ā] Spec k` of `a_X`, the extension by zero
`j_! K` is again in `D^b_c(X̄, ℚ̄_ℓ)`, hence so is `Rā_* j_! K ∈ D^b_c(Spec k, ℚ̄_ℓ)` by the
finiteness theorem (`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`), all of this
computed on the underlying sheaves of `ℚ̄_ℓ`-modules
(`AlgebraicGeometry.ProEtale.mapDerivedCategoryForgetCompRightDerivedLowerStarIso`); and the
global sections of an object of `D^b_c(Spec k, ℚ̄_ℓ)` are perfect
(`AlgebraicGeometry.ProEtale.isPerfect_rightDerivedGlobalSections_forget_of_isAlgClosed`). -/
theorem isPerfect_compactlySupportedGlobalSections_adic
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((compactlySupportedGlobalSections (WeilCoefficients.{u} l) aX).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K)).IsPerfect := by
  let c := HasCompactification.compactification aX
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have hK' : DerivedCategory.boundedAdicConstructible l c.Z
      ((c.i)_!ᵃ[l].mapDerivedCategory.obj K) :=
    ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
      (adicConstructibleSheaf l c.Z).prop_of_iso
        (((c.i)_!ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app K)
        ((hK.2 n).openImmersionLowerShriek c.i)⟩
  have hM : DerivedCategory.boundedAdicConstructible l (Spec (.of k))
      ((c.g)_*ᵃ[l].rightDerivedFunctor.obj ((c.i)_!ᵃ[l].mapDerivedCategory.obj K)) :=
    finiteLowerStar_of_bounded c.g
      (fun _ hF ↦ finiteLowerStar_singleFunctor (𝟙 _) c.g (Fact.out : ringChar k ≠ l) hF)
      _ hK'.1 hK'.2
  have e₁ : (c.i)_!open[WeilCoefficients.{u} l].mapDerivedCategory.obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K) ≅
      (ProEtale.AdicSheaf.forget c.Z).mapDerivedCategory.obj
        ((c.i)_!ᵃ[l].mapDerivedCategory.obj K) :=
    (Functor.mapDerivedCategoryCompIso _ _).symm.app K ≪≫
      (Functor.mapDerivedCategoryNatIso
        (asIso (adicOpenImmersionLowerShriekComparison l c.i))).app K ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app K
  exact (isPerfect_rightDerivedGlobalSections_forget_of_isAlgClosed l _ hM).of_iso
    ((rightDerivedGlobalSections _ _).mapIso
      (((mapDerivedCategoryForgetCompRightDerivedLowerStarIso l c.g).app _).symm ≪≫
        ((c.g)_*[WeilCoefficients.{u} l]).rightDerivedFunctor.mapIso e₁.symm))

omit [HasCompactification aX] in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ(X, K)` is perfect at `ℚ̄_ℓ`.** Let `ℓ` be different from the characteristic of the
algebraically closed field `k`. For `K ∈ D^b_c(X, ℚ̄_ℓ)`, the cohomology `RΓ(X, K)` is a
perfect complex of `ℚ̄_ℓ`-vector spaces: `RΓ(X, K) ≅ RΓ(Spec k, Ra_{X*} K)` (Leray), and
`Ra_{X*} K ∈ D^b_c(Spec k, ℚ̄_ℓ)` by the finiteness theorem
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`). -/
theorem isPerfect_rightDerivedGlobalSections_adic [QuasiCompact aX]
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((rightDerivedGlobalSections (WeilCoefficients.{u} l) X).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K)).IsPerfect := by
  have hM : DerivedCategory.boundedAdicConstructible l (Spec (.of k))
      ((aX)_*ᵃ[l].rightDerivedFunctor.obj K) :=
    finiteLowerStar_of_bounded aX
      (fun _ hF ↦ finiteLowerStar_singleFunctor (𝟙 _) aX (Fact.out : ringChar k ≠ l) hF)
      _ hK.1 hK.2
  have : ((aX)_*[WeilCoefficients.{u} l]).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction _ aX).preservesKInjectiveComplexes
  exact (isPerfect_rightDerivedGlobalSections_forget_of_isAlgClosed l _ hM).of_iso
    ((rightDerivedGlobalSections _ _).mapIso
      ((mapDerivedCategoryForgetCompRightDerivedLowerStarIso l aX).app K).symm ≪≫
      (Functor.rightDerivedFunctorCompIso' _ _
        (globalSectionsLowerStarIso (WeilCoefficients.{u} l) aX)).app _)

omit [IsSeparated aX] [LocallyOfFiniteType aX] in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**The dual of `RΓ_c(X, K)` is perfect at `ℚ̄_ℓ`.** -/
theorem isPerfect_ihom_compactlySupportedGlobalSections_adic
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((ihom ((compactlySupportedGlobalSections (WeilCoefficients.{u} l) aX).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K))).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_compactlySupportedGlobalSections_adic l aX K hK).ihom_unit

omit [HasCompactification aX] in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**The dual of `RΓ(X, K)` is perfect at `ℚ̄_ℓ`.** -/
theorem isPerfect_ihom_rightDerivedGlobalSections_adic [QuasiCompact aX]
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((ihom ((rightDerivedGlobalSections (WeilCoefficients.{u} l) X).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K))).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_rightDerivedGlobalSections_adic l aX K hK).ihom_unit

end Adic

end ProEtale

end AlgebraicGeometry
