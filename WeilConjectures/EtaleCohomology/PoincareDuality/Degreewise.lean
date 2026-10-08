/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-!
# Degreewise Poincaré duality over a field

Let `k` be a separably closed field, `a : X ⟶ Spec k` a morphism admitting a compactification,
`Λ` a finite field whose characteristic is invertible on `X` and `Spec k`, with a Tate twist
datum, and `γ` a Tate orientation of `a` of relative dimension `d`. For `K ∈ D^b_{ctf}(X, Λ)`
perfect over `Λ_X`, the derived Poincaré duality `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing`) gives, in every
degree `i`, an isomorphism of finite-dimensional `Λ`-vector spaces

`H^{2d-i}(X, K^∨(d)) ≅ H^i_c(X, K)^∨`,

and for proper `a` the same with `H_c` replaced by `H`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_of_isPerfectPairing`: over a
  separably closed field, derived global sections carry perfect pairings to dualities.
- `AlgebraicGeometry.Etale.TateOrientation.degreewise_duality` (`sk-thm-derived-duality`,
  `thm-pod-degreewise-perfectness-over-a-field`): degreewise duality over a field.
- `AlgebraicGeometry.Etale.TateOrientation.degreewise_duality_of_isProper`
  (`thm-pod-proper-poincare-duality`, degreewise part): the same for proper `X`, with ordinary
  cohomology.

## Implementation notes

The cohomology groups are the cohomology of the derived global sections
`AlgebraicGeometry.Etale.rightDerivedGlobalSections`, which land in the derived category of
`Λ`-modules; `H^i_c(X, K)` is `AlgebraicGeometry.Etale.compactlySupportedCohomology`.

The blueprint asserts that the adjoint `H^{2d-i}(X, K^∨(d)) ⟶ H^i_c(X, K)^∨` of the degreewise
pairing `⟨-, -⟩_i` is an isomorphism. The degreewise pairing would be obtained from `β_K` through
the lax monoidal structure of `RΓ(Spec k, -)`, which the repository does not have; the
isomorphism is therefore asserted as `Nonempty (_ ≅ _)`, as elsewhere in the six-functor
folder. The line-valued form with values in `Λ(-d)` is not stated separately.

The field stages of the blueprint are `E` and `ℚ̄_ℓ`. The derived duality is available here
only at finite coefficients (the projection formula is stated there), so the field is a finite
field `Λ`, for example `A_{E,1} = 𝒪_E/𝔪_E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- Over a separably closed field `k`, derived global sections carry a perfect pairing
`b : C ⊗ᴸ D ⟶ Λ` in `D(Spec k_ét, Λ)` to a duality `RΓ(Spec k, D) ≅ RΓ(Spec k, C)^∨` in `D(Λ)`.

The pairing identifies `D` with `C^∨`, and derived global sections commute with coefficient
duals. This is part of the identification of the point category `D(Spec k_ét, Λ)` with `D(Λ)`
(blueprint `def-weil-finite-coefficient-point`): since every étale cover of `Spec k` splits,
global sections are a monoidal equivalence between étale sheaves of `Λ`-modules on `Spec k` and
`Λ`-modules, so their derived functor is a monoidal equivalence and preserves internal homs. -/
theorem nonempty_iso_rightDerivedGlobalSections_of_isPerfectPairing
    {C D : DerivedCategoryModule Λ (Spec (.of k))}
    {b : ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C).obj D ⟶ 𝟙_ _}
    (hb : IsPerfectPairing b) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj D ≅
      (ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C)).obj
        (𝟙_ _)) :=
  sorry

variable [IsDomain Λ] [Finite Λ] [HasTateTwist Λ] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)}
  [HasCompactification a] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ (Spec (.of k))]
  {d : ℕ}

variable {Λ}

namespace TateOrientation

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.
This is also blueprint `thm-pod-degreewise-perfectness-over-a-field`.

Let `k` be separably closed, `Λ` a finite field (a finite domain) whose characteristic is
invertible on `X` and on `Spec k`, `γ` a Tate orientation of `a : X ⟶ Spec k` of relative
dimension `d`, and `K ∈ D^b_{ctf}(X, Λ)` perfect over `Λ_X`. Then for every `i` the cohomology
spaces `H^i_c(X, K)` and `H^{2d-i}(X, K^∨(d))` are finite-dimensional and

`H^{2d-i}(X, K^∨(d)) ≅ H^i_c(X, K)^∨`.

It follows from the derived duality `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing`) by taking
`H^{-i}`, the perfect point complex `RΓ_c(X, K)` satisfying `H^{-i}(C^∨) ≅ H^i(C)^∨`
(`DerivedCategory.IsPerfect.nonempty_iso_homology_ihom`). -/
theorem degreewise_duality (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (hKd : IsDualizable K) (i : ℤ) :
    Module.Finite Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K) ∧
      Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K))) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K)) ≅
        ModuleCat.of Λ (Module.Dual Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K))) := by
  have hΛ : IsField Λ := Finite.isField_of_domain Λ
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let C := (R(a)_![ModuleCat.{u + 1} Λ]).obj K
  have hP : (RΓ.obj C).IsPerfect := by
    let _ := hΛ.toField
    rw [DerivedCategory.isPerfect_iff]
    obtain ⟨b₁, b₂, hb⟩ := isZero_compactlySupportedCohomology_of_lt Λ a K hK
    refine ⟨⟨b₁, b₂, ?_, ?_⟩, fun q ↦ finite_compactlySupportedCohomology Λ a K hK q⟩
    · rw [_root_.DerivedCategory.isGE_iff]
      exact fun q hq ↦ hb q (Or.inl hq)
    · rw [_root_.DerivedCategory.isLE_iff]
      exact fun q hq ↦ hb q (Or.inr hq)
  obtain ⟨eA⟩ := nonempty_iso_rightDerivedGlobalSections_of_isPerfectPairing Λ
    (γ.isPerfectPairing_poincarePairing hK hKd)
  obtain ⟨eB⟩ := hP.nonempty_iso_homology_ihom hΛ i
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ a).app _).symm ≪≫
    (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).shiftIso (2 * d : ℤ) (-i)
      (2 * d - i) (by ring)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (-i)).mapIso
      ((RΓ.commShiftIso (2 * d : ℤ)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (-i)).mapIso eA ≪≫ eB
  have hfin : Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      (RΓ.obj C)) := finite_compactlySupportedCohomology Λ a K hK i
  have : Module.Free Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      (RΓ.obj C)) := by
    let _ := hΛ.toField
    exact Module.Free.of_divisionRing _ _
  exact ⟨hfin, Module.Finite.equiv e.toLinearEquiv.symm, ⟨e⟩⟩

/-- Blueprint `thm-pod-proper-poincare-duality`: Proper Poincaré duality (degreewise form).

In the situation of `AlgebraicGeometry.Etale.TateOrientation.degreewise_duality`, if moreover
`a` is proper, then for every `i` the cohomology spaces `H^i(X, K)` and `H^{2d-i}(X, K^∨(d))`
are finite-dimensional and

`H^{2d-i}(X, K^∨(d)) ≅ H^i(X, K)^∨`,

since `RΓ_c(X, K) ≅ RΓ(X, K)` for proper `a`. -/
theorem degreewise_duality_of_isProper [IsProper a] (γ : TateOrientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (hKd : IsDualizable K) (i : ℤ) :
    Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)) ∧
      Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K))) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K)) ≅
        ModuleCat.of Λ (Module.Dual Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ)
          i).obj ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)))) := by
  obtain ⟨hc, hfin, ⟨e⟩⟩ := γ.degreewise_duality hK hKd i
  let f := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).app K) ≪≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ a).app K)
  have : Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))) := hc
  exact ⟨Module.Finite.equiv f.toLinearEquiv, hfin,
    ⟨e ≪≫ f.toLinearEquiv.symm.dualMap.toModuleIso⟩⟩

end TateOrientation

end Etale

end AlgebraicGeometry
