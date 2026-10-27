module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Torsion freeness and injectivity into the bidual

Source: Stacks Project, More on Algebra, Tag 0AV0, clause (3)
(blueprint: lem-per-torsion-free-bidual-injective).
-/

@[expose] public section

universe u v

namespace Module

/-- For a finite module over a domain, the canonical evaluation into its bidual is injective
if and only if the module is torsion free.

Source: Stacks Project, Tag 0AV0, clause (3)
(blueprint: lem-per-torsion-free-bidual-injective).

Proof: If evaluation is injective and `a ≠ 0` annihilates `t`, then every linear functional
`φ : T →ₗ[R] R` satisfies `a * φ t = φ (a • t) = 0`. Cancellation in the domain gives
`φ t = 0`, so evaluation sends `t` to zero and injectivity gives `t = 0`.
Conversely, apply `lem-per-finite-torsion-free-free-embedding` (Stacks Tag 0AUU) to obtain
an injective linear map `i : T →ₗ[R] (Fin r → R)` for some natural number `r`.
Compose `i` with every coordinate projection to obtain linear functionals on `T`.
Equality of the evaluations of `t` and `s` gives equality under all these functionals,
hence coordinatewise equality `i t = i s`, and injectivity of `i` gives `t = s`.
This also covers `r = 0`, since the empty tuple has a unique value. -/
theorem eval_injective_iff_isTorsionFree (R : Type u) (T : Type v)
    [CommRing R] [IsDomain R] [AddCommGroup T] [Module R T] [Module.Finite R T] :
    Function.Injective (Module.Dual.eval R T) ↔ Module.IsTorsionFree R T := by
  sorry

end Module
