module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The ideal quotient defining a controlled transform

Source: the division calculation in Stacks Project, Divisors, Tag 0804, and BMT,
sections 5.1--5.2 (blueprint: def-trf-controlled-transform-ideal).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The largest quasi-coherent ideal whose product with the marking-th power of the
extended center ideal lies in the extended marked ideal. When that power is invertible
and the marked ideal is divisible by it, this is the regular controlled transform.
This construction uses an actual supremum of ideal sheaves, without choosing data from
an existence theorem. Source: Stacks Project, Tag 0804; BMT 5.1--5.2
(blueprint: def-trf-controlled-transform-ideal). -/
def controlledTransformIdeal {X Y : Scheme.{u}} (σ : Y ⟶ X)
    (I J : X.IdealSheafData) (c : ℕ) : Y.IdealSheafData :=
  sSup {K : Y.IdealSheafData | K * (I.comap σ) ^ c ≤ J.comap σ}

end AlgebraicGeometry
