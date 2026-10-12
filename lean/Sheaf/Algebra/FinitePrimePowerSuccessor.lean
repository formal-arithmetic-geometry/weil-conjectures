module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.ZMod.Basic

/-! Successor step for prime-power torsion induction. -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

/--
The successor case in the prime-power extension induction.

Source: Stacks Project, Tag 0F08 (cyclic-coefficient reduction); the explicit
cyclic short exact sequence argument below is an agent-written refinement.

Proof: Put `a = r ^ e`. Since `r` is prime, both `r` and `a` are positive.
Define `i : ℤ/aℤ → ℤ/(a*r)ℤ` by `[x] ↦ [r*x]` and
`q : ℤ/(a*r)ℤ → ℤ/rℤ` by `[y] ↦ [y]`. Changing `x` by a multiple of `a`
changes `r*x` by a multiple of `a*r`, so `i` is well-defined; reduction `q`
is well-defined since `r` divides `a*r`. These additive maps are integer-linear.
If `i([x]) = 0`, divisibility `a*r ∣ r*x` and cancellation of the nonzero
integer `r` give `a ∣ x`, proving injectivity. Every integer representative
of a class modulo `r` is also a representative modulo `a*r`, so `q` is
surjective. Moreover `q([y]) = 0` precisely when `r ∣ y`, precisely when
`[y]` is in the image of `i`; hence the sequence is exact. Lift the maps and
modules by `ULift` and use `r ^ (e + 1) = a*r` to identify its middle term.
Apply `hext` to this short exact sequence, using `hind` and `hprime` on its
end terms and `hiso` for the canonical identifications. For `e = 0`, the
sequence is `0 → ℤ/rℤ → ℤ/rℤ` with identity quotient, so the same argument
also covers the boundary case.
(blueprint: lem-sbc-finite-torsion-prime-power-successor)
-/
theorem finite_torsion_prime_power_successor
    (P : ModuleCat.{u + 1} (ULift.{u + 1} ℤ) → Prop)
    (hiso : ∀ {A B}, (A ≅ B) → P A → P B)
    (hext : ∀ (S : ShortComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))),
      S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (r e : ℕ) (hr : r.Prime)
    (hind : P (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod (r ^ e)))))
    (hprime : P (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod r)))) :
    P (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod (r ^ (e + 1))))) := by
  sorry

end ModuleCat
