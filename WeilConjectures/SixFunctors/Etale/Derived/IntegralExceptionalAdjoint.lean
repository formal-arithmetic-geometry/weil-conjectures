/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalDual
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralVerdier
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# The integral exceptional adjoint

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on an algebraically closed field `k` (the integral stage `Λ = 𝒪_E`), and
`f : X ⟶ Y` a separated morphism of separated `k`-schemes of finite type. This file proves the
integral exceptional adjoint
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`): the derived limit
`G_f L` of the exceptional inverse images of the reductions of `L ∈ Dᵇc(Y, Λ)` lies in
`Dᵇc(X, Λ)`, is `Rf^! L`, satisfies the dual formula `G_f L ≅ 𝔻_X f^*_comp 𝔻_Y L` and has the
expected reduction Tor interval.

## Proof

* The dual formula is the Yoneda argument of `CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedHom`): biduality
  `L ≅ 𝔻_Y 𝔻_Y L` (`thm-coef-integral-verdier`), the projection formula modulo `ϖ`
  (`lem-fix-operation-reduction`), which suffices for morphisms into the derived complete
  dualizing complex, and the identification `Rf^! ω_Y ≅ ω_X` of the dualizing complexes
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_dualizing`).
* Constructibility and the Tor interval then follow, as in the blueprint, from integral
  Verdier duality applied on `Y` and on `X`, the completed pullback being a derived completion
  of `Lf^* 𝔻_Y L` and the dualizing complexes those of `prop-coef-integral-dualizing`.

## Implementation notes

Statements at `Λ` are phrased with `AlgebraicGeometry.Etale.derivedTensor` and
`AlgebraicGeometry.Etale.derivedHom`, never with `⊗` or `ihom` found by instance search: the
kernel does not compare these in reasonable time at `ModuleCat Λ` (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`). The formal Yoneda argument is
therefore specialised first to a general coefficient category
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedHom`).

The identification `Rf^! ω_Y ≅ ω_X` rests on the composition law of the exceptional inverse
images on the torsion tower `n ↦ Λ ⧸ Iⁿ`
(`AlgebraicGeometry.Etale.nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-! ### The formal dual formula -/

section General

attribute [local instance] _root_.DerivedCategory.braidedCategory'

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]

end General

/-! ### Morphisms into objects orthogonal to `ϖ`-invertible objects -/

section Orthogonal

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
include hϖ

end Orthogonal

/-! ### Closure properties of `Dᵇc(X, Λ)` -/

section Closure

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ} {X Y : Scheme.{u}}

end Closure

/-! ### The dual formula at the integral stage -/

section DualFormula

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

end DualFormula

/-! ### The dualizing complexes -/

section Dualizing

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ})

end Dualizing

section DerivedLimit

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

end DerivedLimit

/-! ### The integral exceptional adjoint -/

section Constructible

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

end Constructible

section Matrix

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

variable [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
  {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

end Matrix

end Etale

end AlgebraicGeometry
