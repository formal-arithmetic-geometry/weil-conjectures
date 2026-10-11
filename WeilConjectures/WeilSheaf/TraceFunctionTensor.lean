/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Trace functions and the tensor product with a lisse Weil sheaf

The trace function of a Weil complex is multiplicative under the tensor product with a lisse
Weil sheaf, and the tensor product with a lisse Weil sheaf commutes with pullback.

## Main statements

- `AlgebraicGeometry.WeilComplex.traceFunction_tensorLisse`: `t_{G ⊗ K} = t_G t_K`.
- `AlgebraicGeometry.WeilComplex.nonempty_iso_upperStar_tensorLisse`:
  `φ^*(G ⊗ K) ≅ φ^* G ⊗ φ^* K`.

## Blueprint

These are the properties of the trace function (blueprint `def-fd-trace-function`,
`def-weil-local-frobenius-trace`) used in the proof of the Fourier trace formula
(sketch blueprint `sk-thm-fourier-trace-formula`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- The trace function is multiplicative under the tensor product with a lisse Weil sheaf:
`t_{G ⊗ K} = t_G · t_K`, the local Frobenius on `(G ⊗ K)_x̄ = G_x̄ ⊗ K_x̄` being the tensor
product of the local Frobenius operators. -/
theorem traceFunction_tensorLisse [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l X) (hG : G.IsLisse)
    (K : WeilComplex k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((tensorLisse G hG).obj K).traceFunction n x = G.traceFunction n x * K.traceFunction n x :=
  sorry

/-- Pullback commutes with the tensor product by a lisse Weil sheaf:
`φ^*(G ⊗ K) ≅ φ^* G ⊗ φ^* K`. -/
theorem nonempty_iso_upperStar_tensorLisse (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) (K : WeilComplex k₀ l Y) :
    Nonempty ((upperStar φ).obj ((tensorLisse G hG).obj K) ≅
      (tensorLisse ((WeilSheaf.upperStar φ).obj G)
        (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj ((upperStar φ).obj K)) :=
  sorry


end WeilComplex

end AlgebraicGeometry
