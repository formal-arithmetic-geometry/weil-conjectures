module

public import Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality

/-! # Rational normal curves in their linear spans

Source: Morrison, arXiv:0810.2340, §3.2, Theorem 8 proof step (3).
(blueprint: def-sfb-rational-normal-curve)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed embedded curve is rational normal in its own span when it is P¹ over k,
its hyperplane line pulls back to O(e), and its restricted linear forms have dimension
e + 1. The latter is completeness: H⁰(P¹,O(e)) has dimension e + 1, so the restricted
linear forms give the entire complete system, with only the equations of the span killed.
Source: Morrison §3.2, Theorem 8 step (3); Gieseker, Proposition 1.0.3.
(blueprint: def-sfb-rational-normal-curve) -/
def IsRationalNormalCurve (k : Type u) [Field k] (n : ℕ) {Y : Scheme.{u}}
    (i : Y ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))) (e : ℕ) : Prop :=
  IsClosedImmersion i ∧ 0 < e ∧
    ProjectiveHilbertPolynomial.coordinateDimension k n i 1 = e + 1 ∧
    ∃ α : ℙ(ULift.{u} (Fin 2); Spec (.of k)) ≅ Y,
      α.hom ≫ i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)) =
        (ℙ(ULift.{u} (Fin 2); Spec (.of k)) ↘ Spec (.of k)) ∧
      Nonempty ((Scheme.Modules.tensorPullback (α.hom ≫ i)).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1) ≅
          ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) (e : ℤ))

end AlgebraicGeometry
