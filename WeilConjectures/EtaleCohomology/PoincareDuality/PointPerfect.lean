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

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.
This is also blueprint `thm-pod-point-perfectness` (Point perfectness of global sections), at
the finite stage.

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
This is also blueprint `thm-pod-point-perfectness` (Point perfectness of global sections), at
the finite stage.

**The dual of `RΓ(X, K)` is perfect.** In the situation of
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`, the dual
`RHom_Λ(RΓ(X, K), Λ)` is a perfect complex of `Λ`-modules. -/
theorem isPerfect_ihom_rightDerivedGlobalSections [QuasiCompact aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj
      (𝟙_ _)).IsPerfect :=
  (isPerfect_rightDerivedGlobalSections Λ aX K hK).ihom_unit

/-- Blueprint `thm-pod-point-perfectness`: Point perfectness of global sections, the finite
stage `Λ = A_{E,n}`.

Let `Λ` be a finite ring whose exponent is invertible in the separably closed field `k`, let `X`
be separated of finite type over `k` (neither proper nor smooth) and `K ∈ Dctf(X, Λ)`. Then the
four complexes `RΓ(X, K)`, `RΓ_c(X, K)`, `RΓ(X, K)^∨` and `RΓ_c(X, K)^∨` are perfect point
complexes: bounded complexes of finite projective `Λ`-modules up to quasi-isomorphism. For
proper `X` the two cases are identified by
`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsIsoOfIsProper`.

The explicit Tor amplitude `[a, b + 2d]` of the blueprint is not recorded. -/
theorem isPerfect_globalSections [QuasiCompact aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K).IsPerfect ∧
      ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect ∧
      ((ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj
        (𝟙_ _)).IsPerfect ∧
      ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K)).obj
        (𝟙_ _)).IsPerfect :=
  ⟨isPerfect_rightDerivedGlobalSections Λ aX K hK,
    isPerfect_compactlySupportedGlobalSections Λ aX K hK,
    isPerfect_ihom_rightDerivedGlobalSections Λ aX K hK,
    isPerfect_ihom_compactlySupportedGlobalSections Λ aX K hK⟩

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

variable {I}

/-- An element `r ∈ J` kills the reduction `K ⊗ᴸ (Λ/J)_X`. (A copy of
`AlgebraicGeometry.Etale.smul_id_reductionModIdeal`, whose file imports this one.) -/
private lemma smul_id_reductionModIdeal' {X : Scheme.{u}} {J : Ideal Λ} {r : Λ} (hr : r ∈ J)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    r • 𝟙 ((reductionModIdeal Λ X J).obj K) = 0 := by
  have hM : r • 𝟙 (ModuleCat.of Λ (Λ ⧸ J)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul (Ideal.Quotient.mk J),
      Ideal.Quotient.eq_zero_iff_mem]
    exact J.mul_mem_right _ hr
  change r • 𝟙 (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj _) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul,
    ← (_root_.DerivedCategory.singleFunctor _ 0).map_id, ← Functor.map_smul,
    ← (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map_id, ← Functor.map_smul, hM,
    Functor.map_zero, Functor.map_zero, Functor.map_zero]

/-- The reduction modulo the zero ideal is the identity: `K ⊗ᴸ (Λ/0)_X ≅ K`. -/
noncomputable def reductionModIdealBotIso {X : Scheme.{u}}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (reductionModIdeal Λ X ⊥).obj K ≅ K :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
          (Submodule.quotEquivOfEqBot (⊥ : Submodule Λ Λ) rfl).toModuleIso)) ≪≫
    derivedTensorSingleUnitIso K

variable [IsDomain Λ] [IsPrincipalIdealRing Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- **The transfer of the algebraic perfectness criterion to the point.** Let `Λ` be a principal
ideal domain, complete for the ideal generated by a nonzerodivisor `ϖ`. If an object `N` of
`D(Spec(k)_ét, Λ)` is right orthogonal to the objects on which `ϖ` acts invertibly, and the
reduction `N₁ = cone(ϖ : N ⟶ N)` has perfect derived global sections, then so has `N`. Evaluation
at the point is a `Λ`-linear triangulated equivalence `D(Spec(k)_ét, Λ) ≌ D(Λ)`, so this is
`DerivedCategory.isPerfect_obj_of_rightOrthogonal_of_isPerfect_obj₃`. -/
theorem isPerfect_rightDerivedGlobalSections_of_rightOrthogonal {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) [IsAdicComplete (Ideal.span {ϖ}) Λ]
    {N N₁ : _root_.DerivedCategory
      (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : (_root_.DerivedCategory.smulInvertible (Spec (.of k)).smallEtaleTopology
      ϖ).rightOrthogonal N)
    {g : N ⟶ N₁} {h : N₁ ⟶ N⟦(1 : ℤ)⟧} (hT : Triangle.mk (ϖ • 𝟙 N) g h ∈ distTriang _)
    (hN₁ : ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj N₁).IsPerfect) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj N).IsPerfect := by
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).IsTriangulated :=
    inferInstanceAs (Sheaf.Γ (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).Linear Λ :=
    inferInstanceAs ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.Linear Λ)
  exact _root_.DerivedCategory.isPerfect_obj_of_rightOrthogonal_of_isPerfect_obj₃ _ hϖ hT
    (fun _ f hL ↦ hN f hL) hN₁

variable [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

variable [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [HasCompactification aX]

omit [IsDomain Λ] [IsPrincipalIdealRing Λ] [IsSepClosed k] in
/-- For `I = 0`, the ring `Λ ≅ Λ/I` is finite of exponent invertible in `k`, so the integral
stage is the finite stage. -/
lemma finite_and_hasInvertibleExponent_of_eq_bot (h : I = ⊥) :
    Finite Λ ∧ HasInvertibleExponent Λ (Spec (.of k)) := by
  subst h
  let e : (Λ ⧸ (⊥ : Ideal Λ)) ≃+* Λ := RingEquiv.quotientBot Λ
  refine ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
  obtain ⟨m, hm0, hmΛ, hmk⟩ := HasInvertibleExponent.exists_isUnit_natCast
    (Λ := Λ ⧸ (⊥ : Ideal Λ)) (X := Spec (.of k))
  exact ⟨m, hm0, by simpa using congrArg e hmΛ, hmk⟩

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
    (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l))).out 4 1
  have h' := (Functor.preservesFiniteColimits_tfae
    (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l))).out 1 4
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

end ProEtale

end AlgebraicGeometry
