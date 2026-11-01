/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCartier.NativeCartierRealization
import WeilConjectures.AlgebraicGeometry.NativeCartier.NativeCartierNaturality

/-! # The native equivariant Cartier class

Source: latest blueprint, diagonal-tower-trace proof (1), rank-one Thom proof
Step 1, and the projective-line input of sk-prop-an Step 5(a).
(blueprint: lem-pur-h3-native-cartier-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

namespace AlgebraicGeometry.ProEtale.NativeCartier

/-- There is a canonical positive Cartier class in the ordinary derived category
of equivariant module sheaves, with its strict Kummer-system realization and all
Cartier-preserving pullback squares.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-trace.proof.md, clause (1), and
sk-prop-diagonal-tower-limit.proof.md, clauses (1)--(3).

Proof: The route, geometric-fibre route and ordinary realization fields are
supplied by `native_cartier_route_data`: the normalized strict Kummer system of
the positive extension of the dual Cartier ideal, its total derived limit, the
unique completed-coefficient lift, inversion of ell and extension to Qbar_l, and
exact geometric-fibre descent with its forgetful comparison. The geometric-fibre
projection is a base change of the field extension `k₀ → k̄₀`, hence flat, so the
comapped Cartier ideal is invertible (`IdealSheafData.IsInvertible.comap_of_flat`).
The Cartier-preserving pullback squares are `native_cartier_naturality` applied
to the supplied route data. This argument constructs a native equivariant arrow
and never chooses a lift of a fixed arrow in the ordinary derived category.
(blueprint: lem-pur-h3-native-cartier-class). -/
theorem native_cartier_class (k₀ : Type u) [Field k₀] [Finite k₀]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k₀) :
    Nonempty (Construction k₀ ℓ) := by
  obtain ⟨d⟩ := native_cartier_route_data k₀ ℓ hℓ
  refine ⟨{ route := d.route
            geometricInvertible := ?_
            geometricRoute := d.geometricRoute
            forget := d.forget
            natural := ?_ }⟩
  · intro X J hJ
    have : Flat (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj :=
      CategoryTheory.MorphismProperty.pullback_fst _ _
        (Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance) :
          Flat (Spec.map (CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀)))))
    exact hJ.comap_of_flat _
  · exact native_cartier_naturality k₀ ℓ hℓ d

end AlgebraicGeometry.ProEtale.NativeCartier
