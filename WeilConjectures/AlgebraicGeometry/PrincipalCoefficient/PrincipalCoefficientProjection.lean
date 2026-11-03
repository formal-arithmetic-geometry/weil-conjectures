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

/-- Principal projection comparison.
Source: latest blueprint lem-fix-operation-reduction
(blueprint: lem-principal-coefficient-projection).

Proof: Resolve the quotient by the two-term free uniformizer complex. On K-flat
representatives construct the pullback and tensor comparisons, and on a proper/open
compactification construct the compact-support comparison. Normalize these comparisons
by the scalar adjunction unit. Paste the unit/counit squares defining the projection
map. The pasted square identifies its principal reduction with the projection map
at the fixed scalar extensions, and its two sides are isomorphisms. The zero
quotient at exponent zero gives two zero arrows and is included. -/
theorem principalProjection {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : DE(X, A)) (L : DE(Y, A)) :
    Nonempty (Arrow.mk ((Etale.reductionModIdeal A Y (Ideal.span {a} ^ n)).map
      (Etale.projectionMapApp A f K L)) ≅
      Arrow.mk ((Etale.derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {a} ^ n)) Y).map
        (Etale.projectionMapApp (A ⧸ Ideal.span {a} ^ n) f
          ((extension X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {a} ^ n))).obj K)
          ((extension Y.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {a} ^ n))).obj L)))) := by
  exact CoefficientChange.transformationComparisons.principalProjection ha n f K L

end AlgebraicGeometry.PrincipalCoefficient
