module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Finite sublevels of a positive rational lattice form

Source: Milne, Abelian Varieties, Chapter I, proof of Proposition 14.4(a),
printed p. 62, the bounded-ellipsoid lattice argument
(blueprint: lem-sfb-positive-form-lattice-sublevels-finite).

The rational action on `M ⊗[ℤ] ℚ` is Mathlib's `AddEquiv.module` transport
along the tensor commutor. Thus scalars act on the rational factor, while
lattice elements are inserted in the order `m ⊗ₜ 1` used in the source node.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace LinearMap.BilinForm

/-- A positive definite symmetric rational bilinear form has finite bounded
sublevels on a finite free integer lattice. The finite basis may be empty,
and the rational bound may be negative.

Source: Milne, Abelian Varieties, Chapter I, proof of Proposition 14.4(a),
printed p. 62 (blueprint: lem-sfb-positive-form-lattice-sublevels-finite).

Proof plan:
1. Use the given integer basis and `Module.Basis.baseChange`
   (lem-weil-pbc-free-module-base-change-free), transported along the tensor
   commutor, to obtain the rational basis `b j ⊗ₜ 1`. Integer coordinates
   uniquely determine the original lattice element. An empty basis gives
   the zero module. Bilinearity and positivity imply nonnegative self-values,
   so a negative bound gives the empty set.
2. Apply `LinearMap.BilinForm.exists_orthogonal_basis`
   (lem-sfb-rational-symmetric-form-orthogonal-basis). Writing `d i = B (u i) (u i)`,
   positivity gives `d i > 0`, and orthogonality gives
   `B (∑ i, x i • u i) (∑ i, x i • u i) = ∑ i, d i * (x i)^2`.
3. For a nonnegative bound `c`, every orthogonal coordinate satisfies
   `(x i)^2 ≤ c / d i`, hence `|x i| ≤ 1 + c / d i`. Expand each `u i` in
   the rational basis. The fixed change-of-basis coefficients `a j i` give
   integer coordinates `z j = ∑ i, a j i * x i`, and consequently
   `|z j| ≤ ∑ i, |a j i| * (1 + c / d i)`.
4. Enlarge these finitely many rational bounds to natural-number bounds
   `N j`. Each integer coordinate belongs to the finite interval
   `[-N j, N j]`. The sublevel injects into the finite product of these
   intervals by uniqueness of basis coordinates, and is therefore finite.
-/
theorem finite_lattice_sublevel
    {M : Type u} [AddCommGroup M]
    {ι : Type v} [Finite ι] (_b : Module.Basis ι ℤ M)
    (B : @LinearMap.BilinForm ℚ _ (M ⊗[ℤ] ℚ) _
      ((TensorProduct.comm ℤ M ℚ).toAddEquiv.module ℚ))
    (hsymm : ∀ x y : M ⊗[ℤ] ℚ, B x y = B y x)
    (hpos : ∀ x : M ⊗[ℤ] ℚ, x ≠ 0 → 0 < B x x) (c : ℚ) :
    {m : M | B (m ⊗ₜ[ℤ] (1 : ℚ)) (m ⊗ₜ[ℤ] (1 : ℚ)) ≤ c}.Finite := by
  sorry

end LinearMap.BilinForm
