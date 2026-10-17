/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
public import WeilConjectures.CategoryTheory.DerivedCategory.UniversalCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-!
# The universal coefficient sequences of the Poincaré complexes

Let `Λ` be a commutative ring and `ϖ ∈ Λ` a nonzerodivisor, the intended case being the integral
stage `Λ = 𝒪_E`, `ϖ = ϖ_E`, with finite levels `A_{E,n} = 𝒪_E/ϖⁿ`. For `K ∈ D(X_ét, Λ)` put
`K_n = K ⊗ᴸ (Λ/ϖⁿ)_X` (`AlgebraicGeometry.Etale.reductionModIdeal`). Tensoring the short exact
sequence `0 ⟶ Λ ⟶[ϖⁿ] Λ ⟶ Λ/ϖⁿ ⟶ 0` with `K` gives a distinguished triangle
`K ⟶[ϖⁿ] K ⟶ K_n ⟶ K⟦1⟧`, and its image under any triangulated `Λ`-linear functor
`Φ : D(X_ét, Λ) ⥤ D(Λ)`, such as the compactly supported cohomology `RΓ_c(X, -)` or the
cohomology `RΓ(X, -)`, gives the universal coefficient sequences

`0 ⟶ Hⁱ(Φ K) ⊗_Λ Λ/ϖⁿ ⟶ Hⁱ(Φ K_n) ⟶ Tor₁^Λ(Hⁱ⁺¹(Φ K), Λ/ϖⁿ) ⟶ 0`

of blueprint `prop-pod-integral-degreewise-form`, the Tor term being the `ϖⁿ`-torsion of
`Hⁱ⁺¹(Φ K)` (`DerivedCategory.universalCoefficientSequence`).

## Main statements

- `AlgebraicGeometry.Etale.exists_distinguished_reductionModIdeal`: the triangle
  `K ⟶[ϖⁿ] K ⟶ K_n ⟶ K⟦1⟧`.
- `AlgebraicGeometry.Etale.exists_universalCoefficientSequence_shortExact`: the universal
  coefficient sequences for a triangulated `Λ`-linear `Φ`.
- `AlgebraicGeometry.Etale.exists_universalCoefficientSequence_compactlySupportedGlobalSections`,
  `AlgebraicGeometry.Etale.exists_universalCoefficientSequence_rightDerivedGlobalSections`: the
  cases `Φ = RΓ_c(X, -)` and `Φ = RΓ(X, -)`, the latter to be applied to the second variable
  `K^∨(d)` of the Poincaré pairing.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

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

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- **The triangle of a reduction.** For a nonzerodivisor `ϖ` of `Λ`, `n : ℕ` and
`K ∈ D(X_ét, Λ)`, there is a distinguished triangle `K ⟶[ϖⁿ] K ⟶ K ⊗ᴸ (Λ/ϖⁿ)_X ⟶ K⟦1⟧`: the
tensor product of `K` with `0 ⟶ Λ ⟶[ϖⁿ] Λ ⟶ Λ/ϖⁿ ⟶ 0`. -/
theorem exists_distinguished_reductionModIdeal {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ)
    (K : 𝐃(X, Λ)) :
    ∃ (g : K ⟶ (reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K)
      (h : (reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk (ϖ ^ n • 𝟙 K) g h ∈ distTriang _ := by
  let FX := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  let TX := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ rfl n
  have h₁ : FX.mapTriangle.obj TX ∈ distTriang _ :=
    FX.map_distinguished _ (_root_.DerivedCategory.quotPowTriangle_distinguished _ hϖ rfl n)
  have hX : (FX.mapTriangle.obj TX).mor₁ = ϖ ^ n • 𝟙 (FX.obj TX.obj₁) := by
    rw [Functor.mapTriangle_obj, Triangle.mk_mor₁,
      _root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
      CategoryTheory.Functor.map_id]
  let e : FX.obj TX.obj₁ ≅ K := derivedTensorSingleUnitIso K
  refine ⟨e.inv ≫ (FX.mapTriangle.obj TX).mor₂,
    (FX.mapTriangle.obj TX).mor₃ ≫ e.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ h₁ _ ?_⟩
  refine Triangle.isoMk _ _ e.symm e.symm (Iso.refl _) ?_ (by simp) ?_
  · rw [hX]
    simp
  · simp [← Functor.map_comp]

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form.

**The universal coefficient sequences.** Let `ϖ` be a nonzerodivisor of `Λ` (the integral stage
`Λ = 𝒪_E`), `n : ℕ`, `K ∈ D(X_ét, Λ)` with reduction `K_n = K ⊗ᴸ (Λ/ϖⁿ)_X`, and let
`Φ : D(X_ét, Λ) ⥤ D(Λ)` be a triangulated `Λ`-linear functor (for instance `RΓ_c(X, -)` or
`RΓ(X, -)`). The image under `Φ` of the triangle `K ⟶[ϖⁿ] K ⟶ K_n ⟶ K⟦1⟧` gives, in every
degree `i`, the short exact sequence

`0 ⟶ Hⁱ(Φ K) ⊗_Λ Λ/ϖⁿ ⟶ Hⁱ(Φ K_n) ⟶ Hⁱ⁺¹(Φ K)[ϖⁿ] ⟶ 0`

(`DerivedCategory.universalCoefficientSequence`), where `M[ϖⁿ] = Tor₁^Λ(M, Λ/ϖⁿ)` is the
`ϖⁿ`-torsion of `M`. When `Hⁱ⁺¹(Φ K)` is projective, the first map is an isomorphism
(`DerivedCategory.isIso_universalCoefficientSequence_f_of_projective`). -/
theorem exists_universalCoefficientSequence_shortExact
    (Φ : 𝐃(X, Λ) ⥤ _root_.DerivedCategory (ModuleCat.{u + 1} Λ)) [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [Φ.Linear Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ)
    (K : 𝐃(X, Λ)) (i : ℤ) :
    ∃ (g : Φ.obj K ⟶ Φ.obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K))
      (h : Φ.obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) ⟶ (Φ.obj K)⟦(1 : ℤ)⟧)
      (hT : Triangle.mk (ϖ ^ n • 𝟙 (Φ.obj K)) g h ∈ distTriang _),
      (DerivedCategory.universalCoefficientSequence (ϖ ^ n) g h hT i (i + 1) rfl).ShortExact := by
  obtain ⟨g, h, hT⟩ := exists_distinguished_reductionModIdeal hϖ n K
  have hΦ : Triangle.mk (ϖ ^ n • 𝟙 (Φ.obj K)) (Φ.map g)
      (Φ.map h ≫ (Φ.commShiftIso (1 : ℤ)).hom.app K) ∈ distTriang _ := by
    refine isomorphic_distinguished _ (Φ.map_distinguished _ hT) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp)
    simp [Functor.map_smul]
  exact ⟨_, _, hΦ, DerivedCategory.universalCoefficientSequence_shortExact _ _ _ hΦ _ _ _⟩

section Instances

variable {Y : Scheme.{u}}

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form.

**The universal coefficient sequences for `RΓ_c`.** For `a : X ⟶ Y` admitting a
compactification, a nonzerodivisor `ϖ` of `Λ`, `n : ℕ` and `K ∈ D(X_ét, Λ)`, the sequences

`0 ⟶ Hⁱ_c(X, K) ⊗_Λ Λ/ϖⁿ ⟶ Hⁱ_c(X, K_n) ⟶ Tor₁^Λ(Hⁱ⁺¹_c(X, K), Λ/ϖⁿ) ⟶ 0`

are short exact, where `Hⁱ_c(X, -) = Hⁱ(RΓ_c(X, -))` and `Tor₁^Λ(M, Λ/ϖⁿ)` is the
`ϖⁿ`-torsion of `M`. -/
theorem exists_universalCoefficientSequence_compactlySupportedGlobalSections (a : X ⟶ Y)
    [HasCompactification a] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (K : 𝐃(X, Λ))
    (i : ℤ) :
    ∃ (g : (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K ⟶
        (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K))
      (h : (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) ⟶
        ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K)⟦(1 : ℤ)⟧)
      (hT : Triangle.mk
        (ϖ ^ n • 𝟙 ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K)) g h ∈
          distTriang _),
      (DerivedCategory.universalCoefficientSequence (ϖ ^ n) g h hT i (i + 1) rfl).ShortExact := by
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).IsTriangulated :=
    inferInstanceAs
      (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).Linear Λ :=
    inferInstanceAs
      ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.Linear Λ)
  have : (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).IsTriangulated :=
    inferInstanceAs ((R(a)_![ModuleCat.{u + 1} Λ] ⋙
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).IsTriangulated)
  have : (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).Linear Λ :=
    inferInstanceAs ((R(a)_![ModuleCat.{u + 1} Λ] ⋙
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).Linear Λ)
  exact exists_universalCoefficientSequence_shortExact _ hϖ n K i

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form.

**The universal coefficient sequences for `RΓ`.** For a nonzerodivisor `ϖ` of `Λ`, `n : ℕ` and
`M ∈ D(X_ét, Λ)` (in the Poincaré pairing, the second variable `M = K^∨(d)`), the sequences

`0 ⟶ Hⁱ(X, M) ⊗_Λ Λ/ϖⁿ ⟶ Hⁱ(X, M_n) ⟶ Tor₁^Λ(Hⁱ⁺¹(X, M), Λ/ϖⁿ) ⟶ 0`

are short exact, `Tor₁^Λ(-, Λ/ϖⁿ)` being the `ϖⁿ`-torsion. -/
theorem exists_universalCoefficientSequence_rightDerivedGlobalSections {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (M : 𝐃(X, Λ)) (i : ℤ) :
    ∃ (g : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj M ⟶
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj M))
      (h : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj M) ⟶
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj M)⟦(1 : ℤ)⟧)
      (hT : Triangle.mk
        (ϖ ^ n • 𝟙 ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj M)) g h ∈
          distTriang _),
      (DerivedCategory.universalCoefficientSequence (ϖ ^ n) g h hT i (i + 1) rfl).ShortExact := by
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
    inferInstanceAs
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).Linear Λ :=
    inferInstanceAs
      ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.Linear Λ)
  exact exists_universalCoefficientSequence_shortExact _ hϖ n M i

end Instances

end Etale

end AlgebraicGeometry
