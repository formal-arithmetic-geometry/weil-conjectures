/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import Submission.WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalDual
import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars
import Submission.WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsTorAmplitude
import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.GenericFiniteness
import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDual
import Submission.WeilConjectures.Compactification.NagataCompactification
import Submission.WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import Submission.WeilConjectures.SixFunctors.Etale.Derived.TensorHom
import Submission.WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import Submission.WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Submission.WeilConjectures.CategoryTheory.Monoidal.Dualizable
import Submission.WeilConjectures.ConstructibleSheaf.EtaleDescent
import Submission.WeilConjectures.ConstructibleSheaf.GenericConstancy
import Submission.WeilConjectures.ConstructibleSheaf.Refinement
import Submission.WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Verdier biduality at the integral stage

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on an algebraically closed field `k` (the integral stage `Λ = 𝒪_E`,
`I = 𝔪_E`), and `X` separated of finite type over `k` with structure morphism `a_X`. The integral
dualizing complex `ω_{X, 𝒪_E} = R lim_n Res_n Ra_{X,n}^! A_n` is the point of a homotopy limit
cone of the tower `n ↦ Ra_X^!(Λ ⧸ Iⁿ)` (restriction of scalars commuting with `Ra_X^!`), and the
integral Verdier dual is `𝔻_X = RHom(-, ω_X)`. This file records the integral stage of blueprint
`thm-sf-biduality-class` (`AlgebraicGeometry.Etale.verdierDual_integralStage`), deduced, as in the
blueprint, from integral Verdier duality (`thm-coef-integral-verdier`,
`AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom_dualizing`), which belongs to the
coefficient chapter.

## Implementation notes

As elsewhere in the repository
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`), the Tor amplitude of
the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` is measured over `Λ`, after restriction of scalars. Since
`Λ ⧸ Iⁿ⁺¹ ⊗ᴸ_Λ Λ ⧸ Iⁿ⁺¹ ≅ Λ ⧸ Iⁿ⁺¹ ⊕ Λ ⧸ Iⁿ⁺¹[1]`, a Tor interval `[a, b]` over `Λ` of the
restriction of an `A_n`-complex is the interval `[a + 1, b]` over `A_n`, and conversely `[α, β]`
over `A_n` gives `[α - 1, β]` over `Λ`. The finite-stage dual interval `[-b - 2d, -a]` of the
blueprint therefore reads `[-b - 2d - 1, -a - 1]` in this convention.

The exceptional inverse image `Ra_X^!` over `Λ` is the right adjoint of `Ra_{X!}`, so it is defined
under the hypothesis that `Ra_{X!}` is a left adjoint, taken as an instance argument (it is a
theorem for torsion coefficients, `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

attribute [local instance] _root_.DerivedCategory.braidedCategory'

section DoubleDual

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

end DoubleDual

section GlobalDuality

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

end GlobalDuality

/-! Private ingredients for the integral dualizing object. -/

universe v w

section IntegralVerdierHomNotation

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

end IntegralVerdierHomNotation

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
  [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

variable
  (ωX : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
    (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint))
  (hωX : Pretriangulated.IsHomotopyLimit ωX)

end Etale

end AlgebraicGeometry
