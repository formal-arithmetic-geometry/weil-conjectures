/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Vanishing
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-!
# The closed-support triangle on `Dᵇc(-, 𝒪_E)`

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on a field `k`: the integral stage `Λ = 𝒪_E`, `I = 𝔪_E` of the `ℓ`-adic
formalism. The category `Dᵇc(X, Λ)` is
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral I X`: the objects of
`D(X_ét, Λ)` which are derived complete for `I` and whose reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` are bounded
constructible of Tor amplitude in one common interval.

This file proves the ingredients of clauses (1)–(4) and (1')–(4') of blueprint
`prop-sf-localization-all-stages` at the integral stage, for a closed immersion `i : Z ⟶ X` and
the complementary quasi-compact open immersion `j : U ⟶ X` of schemes of finite type over `k`:
the stability of `Dᵇc(-, Λ)` under the operations, its triangulated structure, the supported
localization triangle on `D(X_ét, Λ)`, and the closed-support triangle on `Dᵇc(-, Λ)` under the
hypotheses providing an exceptional adjunction `Ri_! ⊣ Ri^!` on `D(X_ét, Λ)`. The right adjoint
of `i_*` on `Dᵇc(-, Λ)` without those hypotheses is constructed in
`WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport`.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isTriangulated_boundedConstructibleIntegral`:
  `Dᵇc(X, Λ)` is a triangulated subcategory of `D(X_ét, Λ)`.
- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedLowerStar_obj`: `Rf_*`
  preserves `Dᵇc(-, Λ)` (clause (1)).
- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_of_rightDerivedLowerStar_obj`: `Ri_*`
  detects `Dᵇc(-, Λ)`.
- `AlgebraicGeometry.Etale.torAmplitudeIn_reductionModIdeal_of_distTriang`: the Tor amplitude
  bound of clause (2').
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated Opposite

open scoped CategoryTheory.Functor

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

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ}

/-! ### Tor amplitude and closure properties -/

section Triangulated

section TorAmplitude

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

end TorAmplitude

variable {X : Scheme.{u}}

variable [IsNoetherianRing Λ] [Finite (Λ ⧸ I)]

end Triangulated

/-! ### Derived completeness through adjunctions

An object is derived complete for `I = (ϖ)` exactly when it receives no nonzero map from an
object on which `ϖ` acts invertibly (`DerivedCategory.derivedComplete_iff_rightOrthogonal`). A
right adjoint of a `Λ`-linear functor therefore preserves derived completeness. -/

section DerivedComplete

variable {X Y : Scheme.{u}} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
include hϖ hI

end DerivedComplete

/-! ### The reductions of the operations -/

section Reductions

variable {X Y : Scheme.{u}} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
include hϖ hI

variable [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] {k : Type u} [Field k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [LocallyOfFiniteType aY] [QuasiCompact aY]

end Reductions

/-! ### The ambient recollement data

The facts behind the supported localization triangle on the whole of `D(X_ét, Λ)`
(`AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`), in the form used by
`CategoryTheory.Pretriangulated.Recollement`. -/

section Recollement

variable {U Z X : Scheme.{u}}

end Recollement

/-! ### The exceptional inverse image on `Dᵇc(-, Λ)` -/

section UpperShriek

variable [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
  {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X Y : Scheme.{u}}

end UpperShriek

/-! ### The closed-support triangle at the integral stage -/

section Localization

variable {U Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

variable [HasCompactification i] [(R(i)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

end Localization

/-! ### `Dᵇc(-, 𝒪_E)` -/

section BoundedConstructible

variable {U Z X Y : Scheme.{u}} [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] {k : Type u} [Field k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

end BoundedConstructible

section Triangle

variable {U Z X : Scheme.{u}} [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ]
  [Finite (Λ ⧸ I)] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
  (aX : X ⟶ Spec (.of k)) (aZ : Z ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
  [IsSeparated aX] [IsSeparated aZ] [HasCompactification aX] [HasCompactification aZ]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aZ)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
  (i : Z ⟶ X) (hi : i ≫ aX = aZ) [IsClosedImmersion i] [HasCompactification i]
  [(R(i)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

end Triangle

end Etale

end AlgebraicGeometry
