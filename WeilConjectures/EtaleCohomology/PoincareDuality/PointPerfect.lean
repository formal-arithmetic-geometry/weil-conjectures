/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek

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

At `ℚ̄_ℓ`, for `ℓ` different from the characteristic of `k` and pro-étale complexes with
constructible `ℓ`-adic cohomology sheaves:

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
as in the definition of `AlgebraicGeometry.WeilComplex`.
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
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
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

omit [IsSeparated aX] in
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

omit [IsSeparated aX] in
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
stage `Λ = 𝒪_E`, `I = 𝔪_E` for `E` finite over `ℚ_ℓ`. For `K ∈ D^b_c(X, Λ)`, the compactly
supported cohomology `RΓ_c(X, K)` is a perfect complex of `Λ`-modules. Its reductions are the
`RΓ_c(X, K ⊗ᴸ Λ/Iⁿ)`, perfect of one common amplitude by the finite stage
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`; and `RΓ_c(X, K)` is
derived complete (`AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerShriek`), hence the
derived limit of its reductions, which is perfect (the uniform-tower reconstruction
`lem-weil-pbc-reconstruction-uniform-tower`). -/
theorem isPerfect_compactlySupportedGlobalSections_integral (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect :=
  sorry

omit [IsSeparated aX] in
/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ(X, K)` is perfect at the integral stage.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral`, the cohomology
`RΓ(X, K)` is a perfect complex of `Λ`-modules. As at the finite stage, for a compactification
`X ⟶[j] X̄ ⟶[ā] Spec k` of `a_X` one has `RΓ(X, K) ≅ RΓ_c(X̄, Rj_* K)`, and
`Rj_* K ∈ D^b_c(X̄, Λ)`: `Rj_*` preserves derived completeness, commutes with the reductions,
and carries Tor amplitude `[a, b]` to `[a, b + 2 dim X]`. -/
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
        (torAmplitudeIn_rightDerivedLowerStar _ aX c.g c.i c.comm.symm d hd a b _ hN hNY hbc hta)⟩
  exact (isPerfect_compactlySupportedGlobalSections_integral I c.g hI _ hK').of_iso
    ((compactlySupportedGlobalSectionsIsoOfIsProper _ c.g).app _ ≪≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ c.i).app K)

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**The dual of `RΓ_c(X, K)` is perfect at the integral stage.** -/
theorem isPerfect_ihom_compactlySupportedGlobalSections_integral (hI : I.IsPrincipal)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_compactlySupportedGlobalSections_integral I aX hI K hK).ihom_unit

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
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
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
  · exact (isPerfect_compactlySupportedGlobalSections_integral I aX hI K hK).tensor_homology E
  · exact (isPerfect_rightDerivedGlobalSections_integral I aX hI K hK).tensor_homology E
  · exact (isPerfect_ihom_compactlySupportedGlobalSections_integral I aX hI K hK).tensor_homology
      E
  · exact (isPerfect_ihom_rightDerivedGlobalSections_integral I aX hI K hK).tensor_homology E

end Integral

end Etale

namespace ProEtale

section Adic

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [IsSepClosed k] [Fact (ringChar k ≠ l)]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [HasCompactification aX]

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ_c(X, K)` is perfect at `ℚ̄_ℓ`.** Let `ℓ` be different from the characteristic of `k`.
For `K ∈ D^b_c(X, ℚ̄_ℓ)`, the compactly supported
cohomology `RΓ_c(X, K)` is a perfect complex of `ℚ̄_ℓ`-vector spaces: bounded with finite
dimensional cohomology. The complex `K` is defined over the ring of integers of a finite
extension `E/ℚ_ℓ`, and the statement follows from the integral stage
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_integral` by flat
extension of scalars `𝒪_E → E → ℚ̄_ℓ`. -/
theorem isPerfect_compactlySupportedGlobalSections_adic
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((compactlySupportedGlobalSections (WeilCoefficients.{u} l) aX).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K)).IsPerfect :=
  sorry

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ(X, K)` is perfect at `ℚ̄_ℓ`.** Let `ℓ` be different from the characteristic of `k`.
For `K ∈ D^b_c(X, ℚ̄_ℓ)`, the cohomology `RΓ(X, K)` is a
perfect complex of `ℚ̄_ℓ`-vector spaces, by flat extension of scalars from
`AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections_integral`. -/
theorem isPerfect_rightDerivedGlobalSections_adic [QuasiCompact aX]
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((rightDerivedGlobalSections (WeilCoefficients.{u} l) X).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K)).IsPerfect :=
  sorry

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**The dual of `RΓ_c(X, K)` is perfect at `ℚ̄_ℓ`.** -/
theorem isPerfect_ihom_compactlySupportedGlobalSections_adic
    (K : _root_.DerivedCategory (ProEtale.AdicSheaf l X))
    (hK : DerivedCategory.boundedAdicConstructible l X K) :
    ((ihom ((compactlySupportedGlobalSections (WeilCoefficients.{u} l) aX).obj
      ((ProEtale.AdicSheaf.forget X).mapDerivedCategory.obj K))).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_compactlySupportedGlobalSections_adic l aX K hK).ihom_unit

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
