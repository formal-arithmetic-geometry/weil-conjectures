/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrincipalCoefficient.PrincipalCoefficientUniversalPair
import WeilConjectures.AlgebraicGeometry.CoefficientChange.CoefficientTransformationComparisons

/-! # A principal coefficient comparison

Source: latest blueprint lem-fix-operation-reduction, proof of the principal
coefficient-change comparisons. The coefficient quotient has a finite free
resolution; its extension functor is the constructed fixed scalar adjoint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor
attribute [local instance 2000] CommRing.toRing
namespace AlgebraicGeometry.PrincipalCoefficient
set_option hygiene false in
local notation "DE(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} A))
set_option hygiene false in
local notation "DP(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

/-- Principal exchange comparison.
Source: latest blueprint lem-fix-operation-reduction
(blueprint: lem-principal-coefficient-exchange).

Proof: Resolve the principal quotient by its two-term free complex. Proper pushforward
commutes with this finite coefficient complex, and open extension commutes termwise
with coefficient change. Paste these squares with the pullback square for the
cartesian diagram. Naturality of the adjunction counit identifies the resulting
map with the compact-support exchange map for the same compactification. The two
object comparisons are invertible, including exponent zero. -/
theorem principalExchange {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : DP(X, A)) :
    Nonempty (Arrow.mk
      ((_root_.DerivedCategory.reductionModIdeal (Scheme.ProEt.topology Y')
        (Ideal.span {a} ^ n)).map
        ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app K)) ≅
      Arrow.mk ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y')
        (Ideal.Quotient.mk (Ideal.span {a} ^ n))).map
        ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) sq c).app
            ((extension (Scheme.ProEt.topology X)
              (Ideal.Quotient.mk (Ideal.span {a} ^ n))).obj K)))) := by
  exact CoefficientChange.transformationComparisons.principalExchange ha n sq c K

end AlgebraicGeometry.PrincipalCoefficient
