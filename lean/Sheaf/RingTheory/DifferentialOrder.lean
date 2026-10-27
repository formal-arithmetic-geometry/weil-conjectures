module

public import Mathlib.Algebra.Algebra.Tower

/-!
# The recursive order bound for algebraic differential operators

Source: Stacks Project, Algebra, Definition 09CI, `definition-differential-operators`
(blueprint: def-trf-differential-order).
-/

@[expose] public section

universe u v w z

namespace LinearMap

/-- Differential order at most `n` over the commutative algebra `C/R`, for maps between
`C`-modules with their compatible restricted `R`-module structures. At order zero the map
commutes with every `C`-scalar; at successor order each scalar commutator has the preceding
bound. Here `Algebra.lsmul R R M c` is multiplication by `c` on `M`.
Source: Stacks Project, Algebra, Definition 09CI (blueprint: def-trf-differential-order). -/
def HasDifferentialOrderLE (R : Type u) (C : Type v) [CommRing R] [CommRing C]
    [Algebra R C] {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
    [Module C M] [Module C N] [Module R M] [Module R N]
    [IsScalarTower R C M] [IsScalarTower R C N] (n : ℕ) (D : M →ₗ[R] N) : Prop :=
  match n with
  | 0 => ∀ (c : C) (x : M), D (c • x) = c • D x
  | n + 1 => ∀ c : C, HasDifferentialOrderLE R C n
      (D.comp (Algebra.lsmul R R M c) - (Algebra.lsmul R R N c).comp D)

end LinearMap
