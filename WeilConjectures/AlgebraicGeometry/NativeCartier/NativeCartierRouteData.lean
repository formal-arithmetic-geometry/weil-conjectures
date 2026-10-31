/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCartier.NativeCartierRealization

/-! # Route and geometric data for the native Cartier construction

Source: latest blueprint, diagonal-tower-trace proof (1).
(blueprint: lem-pur-native-cartier-route-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Endofunctor
namespace AlgebraicGeometry.ProEtale.NativeCartier
open SpTowerClasses DiagonalCoefficients

/-- The route, geometric-fibre, and ordinary-realization fields of a native Cartier
construction, before its pullback naturality field is supplied.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-trace.proof.md, clause (1).
Proof: construct the normalized strict Kummer route, its geometric-fibre route,
and the coefficient and Tate realization comparison for every Cartier ideal.
The construction uses the integral quotient tower, total derived inverse limit,
completed coefficient realization, and the three normalized scalar extensions.
The geometric-fibre comparison is obtained by exact inverse-image descent.
All comparison equations are the displayed equations in `Construction.forget`.
This is strictly the data portion of `Construction`; its pullback naturality is
left to a separate theorem.
(blueprint: lem-pur-native-cartier-route-data). -/
structure RouteData (k₀ : Type u) [Field k₀] [Finite k₀]
    (ℓ : ℕ) [Fact ℓ.Prime] where
  route : ∀ (X : Base k₀) (J : X.scheme.IdealSheafData) (hJ : J.IsInvertible),
    OrdinaryRoute ℓ X.scheme (divisorPic J hJ)
  geometricInvertible : ∀ (X : Base k₀) (J : X.scheme.IdealSheafData)
    (_hJ : J.IsInvertible),
    (J.comap (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).IsInvertible
  geometricRoute : ∀ (X : Base k₀) (J : X.scheme.IdealSheafData) (hJ : J.IsInvertible),
    OrdinaryRoute ℓ (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (divisorPic (J.comap (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
        (geometricInvertible X J hJ))
  forget : ∀ (X : Base k₀) (J : X.scheme.IdealSheafData) (hJ : J.IsInvertible),
    ∃ e : (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
        (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).obj
        (spQbarTwist X.scheme ℓ) ≅
      spQbarTwist (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiber ℓ,
    IsTatePullback ℓ (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj e ∧
    HEq (mapSingleArrow (Endofunctor.IsoAlgebra.forget (frobenius k₀ ℓ X.scheme)) (2 : ℤ)
        (nativeClass k₀ ℓ X.scheme (route X J hJ)))
      ((DerivedCategory.singleFunctor _ 0).map
          (CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj.{u} ℓ)
            (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).hom ≫
        (geometricRoute X J hJ).class ≫
        ((DerivedCategory.singleFunctor _ 0).map e.inv)⟦(2 : ℤ)⟧')

/-- The route and geometric realization data exist.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-trace.proof.md, clause (1).
Proof: apply the normalized integral Kummer construction over every quasi-compact,
quasi-separated finite-type scheme, then apply exact geometric-fibre descent and
its normalized coefficient and Tate comparisons. The Cartier ideal pullback remains
invertible on the geometric fibre, and the resulting ordinary arrow is the
prescribed forgetful image. This theorem supplies only the four data fields of
`RouteData`, so it is strictly weaker than the full native construction.
(blueprint: lem-pur-native-cartier-route-data). -/
theorem native_cartier_route_data (k₀ : Type u) [Field k₀] [Finite k₀]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k₀) :
    Nonempty (RouteData k₀ ℓ) := by
  sorry

end AlgebraicGeometry.ProEtale.NativeCartier
