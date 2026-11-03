/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeWeilDerivedFramework
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection

/-!
# Frobenius equivariance of the compactification projection

Source: latest blueprint, `lem-fix-weil-operations.proof.md`, last paragraph:
“the projection transformation of [def-exchange-projection] is a composite of
precisely these tensor and counit maps, hence is equivariant as well”.
(blueprint: lem-fix-projection-compactification-comparison)

The theorem uses the prescribed finite-field coefficient, geometric Frobenius
and a finite-field compactification. Every structure map in its conclusion is
the displayed canonical construction: pullback is the Frobenius-square lift,
the tensor is `wfCondensedTensorFrobenius`, compact support is the
open-extension/proper-direct-image exchange, and the projection is the native
`exchangeProjectionData` component. No Weil structure or projection arrow is
an unconstrained hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

set_option maxHeartbeats 1600000 in
-- Native derived-functor comparisons require a larger elaboration budget.
/-- The canonical compactification projection is a morphism of the induced
geometric-Frobenius pairs.

Source: latest blueprint, `lem-fix-weil-operations.proof.md`, final paragraph,
"the projection transformation ... is equivariant as well".
(blueprint: lem-fix-projection-compactification-comparison)

Proof (postponed), following the five source steps. (1) Factor the geometric
fibre map through the displayed compactification. The compact-support map is
`Rp_*(γ)π_p`, with `γ` the normalized open tensor comparison, and the exchange
and identity/inverse equations identify its Frobenius structure with the
canonical `Rf_!` structure. (2) For the proper factor, use the native
Frobenius-pair adjunction; its pullback tensor comparison is monoidal, so the
derived tensor comparison and tensors of pair maps commute with Frobenius.
(3) The proper projection is the adjoint transpose of `(ε ⊗ 1) d`; the
counit and the unit are pair maps, hence this transpose is a pair map without
any invertibility assertion. (4) The normalized open tensor comparison and open
Frobenius comparison restrict to identities. The `j_! ⊣ j^*` Hom bijection and
the invertible open unit lift the equality from the open back to the
compactification. (5) Proper direct image preserves pair maps, and composing
its equation with the equation for `π_p` gives the displayed projection square.
The bounded-constructible and finite-Tor domains are preserved by the
stipulated operations.

The edge cases of an identity or empty geometric fibre and zero inputs are
included; the statement does not assert that the projection is invertible. -/
theorem projection_compactification_frobenius_equivariant
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (c : WeilCoefficient ell)
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c₀ : Compactification f₀.left)
    (K : strictWeilComplexCategory D ell hEll X₀ c)
    (L : strictWeilComplexCategory D ell hEll Y₀ c)
    (hL : condensedConstructibleFiniteTor (WeilCoefficient.ab c)
      (D.geometricFiber Y₀).left L.obj.carrier) :
    let X := (D.geometricFiber X₀).left
    let Y := (D.geometricFiber Y₀).left
    let f := D.geometricFiberMap f₀
    let gX := (D.geometricFrobenius X₀).hom
    let gY := (D.geometricFrobenius Y₀).hom
    let Λ : Profinite.CondensedRing.{u} := ⟨WeilCoefficient.ab c⟩
    let c' := constantTwistGeometricCompactification D f₀ c₀
    let sqP := nativeWeilGeometricSquare D
      (nativeWeilCompactificationProper D f₀ c₀)
    let sqJ := nativeWeilGeometricSquare D
      (nativeWeilCompactificationOpen D f₀ c₀)
    let P := constantTwistPullbackPair Λ f
      (nativeWeilGeometricSquare D f₀) L.obj
    let T := Endofunctor.IsoAlgebra.mk
      ((wfCondensedTensor Λ.X X).obj (K.obj.carrier, P.carrier))
      (wfCondensedTensorFrobenius Λ.X gX K.obj P)
    let supportStructure := fun M ↦ constantTwistSupportStructureMap Λ c' sqP sqJ M
    let FK := (rightDerivedLowerShriekOfCompactification Λ.X c').obj K.obj.carrier
    let FT := (rightDerivedLowerShriekOfCompactification Λ.X c').obj T.carrier
    let thetaSource :=
      (wfCondensedTensorPullback Λ.X gY FK L.obj.carrier).hom ≫
        (wfCondensedTensor Λ.X Y).map
          (Prod.mkHom (supportStructure K.obj) L.obj.str.hom)
    let projection := (exchangeProjectionData Λ.X c' gY).projection
      K.obj.carrier L.obj.carrier
    boundedConstructible (condensedRingObj Λ.X X) P.carrier →
    boundedConstructible (condensedRingObj Λ.X X) T.carrier →
    boundedConstructible (condensedRingObj Λ.X Y) FK →
    boundedConstructible (condensedRingObj Λ.X Y) FT →
    boundedConstructible (condensedRingObj Λ.X Y)
      ((wfCondensedTensor Λ.X Y).obj (FK, L.obj.carrier)) →
    thetaSource ≫ projection =
      (wfCondensedFrobenius Λ.X gY).map projection ≫ supportStructure T := by
  sorry

end WeilConjectures
