/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCartier.NativeCartierRouteData

/-! # Pullback naturality for the native Cartier construction

Source: latest blueprint, diagonal-tower-trace proof (1).
(blueprint: lem-pur-native-cartier-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.NativeCartier
open SpTowerClasses

/-- Pullback naturality for supplied route and geometric realization data.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-trace.proof.md, clause (1).
Proof: pull a regular Cartier equation back along the given morphism and compare
its dual line with the dual pulled-back ideal. The strict Kummer extension,
derived limit, completed lift, scalar adjunctions, and exact equivariant descent
all commute with this comparison. Their normalized coefficient and Tate endpoint
maps therefore form `PullbackEndpoints`, and exact functoriality gives the
 displayed native arrow equation. This theorem supplies only the final naturality
field after the route data have been supplied.
(blueprint: lem-pur-native-cartier-naturality). -/
theorem native_cartier_naturality (k₀ : Type u) [Field k₀] [Finite k₀]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k₀)
    (d : RouteData k₀ ℓ) :
    ∀ (X Y : Base k₀) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (CommRingCat.of k₀))]
      (J : Y.scheme.IdealSheafData) (hJ : J.IsInvertible)
      (hJ' : (J.comap f).IsInvertible),
      ∃ e : PullbackEndpoints k₀ ℓ f,
      HEq (mapSingleArrow (pull k₀ ℓ f) (2 : ℤ)
        (nativeClass k₀ ℓ Y.scheme (d.route Y J hJ)))
      ((DerivedCategory.singleFunctor _ 0).map e.coefficient.hom ≫
        nativeClass k₀ ℓ X.scheme (d.route X (J.comap f) hJ') ≫
        ((DerivedCategory.singleFunctor _ 0).map e.line.inv)⟦(2 : ℤ)⟧') := by
  sorry

end AlgebraicGeometry.ProEtale.NativeCartier
