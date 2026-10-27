module

public import Mathlib.Algebra.Algebra.Tower

/-!
# Finite differential order of module maps

Source: Stacks Project, algebra.tex, Tag 09CI, definition-differential-operators.
(blueprint: def-trf-differential-operator-order)
-/

@[expose] public section

universe u v w z

namespace LinearMap

/-- The scalar commutator sends `x` to `T (c • x) - c • T x`.
Source: Stacks Project, algebra.tex, Tag 09CI, definition-differential-operators.
(blueprint: def-trf-differential-operator-order) -/
def scalarCommutator {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
    [Module C M] [Module C N] [Module R M] [Module R N]
    [IsScalarTower R C M] [IsScalarTower R C N] (T : M →ₗ[R] N) (c : C) : M →ₗ[R] N :=
  T.comp (Algebra.lsmul R R M c) - (Algebra.lsmul R R N c).comp T

/-- An `R`-linear map has differential order at most zero if it is `C`-linear;
its order is at most `n + 1` if every scalar commutator has order at most `n`.
The compatible `R`-module structures are restriction of scalars along `R → C`.
Source: Stacks Project, algebra.tex, Tag 09CI, definition-differential-operators.
(blueprint: def-trf-differential-operator-order) -/
def IsDifferentialOperatorOfOrderLE (R : Type u) (C : Type v)
    [CommRing R] [CommRing C] [Algebra R C]
    {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
    [Module C M] [Module C N] [Module R M] [Module R N]
    [IsScalarTower R C M] [IsScalarTower R C N] (n : ℕ) (T : M →ₗ[R] N) : Prop :=
  match n with
  | 0 => ∀ (c : C) (x : M), T (c • x) = c • T x
  | n + 1 => ∀ c : C, IsDifferentialOperatorOfOrderLE R C n (scalarCommutator T c)

end LinearMap
