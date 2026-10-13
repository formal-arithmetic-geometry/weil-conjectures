/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Sheaf.Paper.TorsionModuleFlatBaseChangeIso
import Sheaf.RingTheory.TorsionHomFlatComparison
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Lifting maps from an ideal power modulo principal maps

Source: Stacks Project, Tags 05ED--05EG, especially the two right arrows of the
05EG diagram (blueprint: lem-weil-pbc-ideal-power-hom-lift).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace LinearMap

/-- A map from `I^n` to the scalar extension of `N` lifts modulo a principal map.
Source: Stacks Project, Tag 05EG, second paragraph, with Tags 05ED, 05EE, 05EF,
05E9 and 05EC (blueprint: lem-weil-pbc-ideal-power-hom-lift).

Proof: choose finitely many generators `f_i` of `J = I^n`. Evaluate `d` on them;
the resulting tuple is a Koszul one-cycle, and its map from the naive Koszul
presentation vanishes on the kernel `K` of the map to `R`. Flatness identifies
one-cycle homology after tensoring with the one-cycle homology over `S`.
The homology over `R` is killed by `J` (05EF), so 05E9 makes its canonical
base-change map bijective. Lift the class of the evaluated tuple to a cycle `y`
over `R`. Equality of the classes supplies `m` with `1 ⊗ y_i = d(f_i) + f_i m`.
The base-changed map defined by `y` vanishes on `K`: the map defined by `d`
does, and the principal correction factors through the map to `R`. The module
`K` is killed by `J` (05ED); the injectivity of the Hom comparison in 05EC
therefore shows that the map defined by `y` already vanishes on `K` over `R`.
It factors through `J`, giving `l : J → N`. The required identity holds on
all generators, hence on their span. The zero ideal gives the zero map;
for the unit ideal every map is principal, so the same statement applies. -/
theorem exists_ideal_power_hom_lift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat) (I : Ideal R) (_hI : I.FG)
    (_hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) (_hn : 1 ≤ n)
    {N : Type w} [AddCommGroup N] [Module R N]
    (d : ↥(I ^ n) →ₗ[R] S ⊗[R] N) :
    ∃ (l : ↥(I ^ n) →ₗ[R] N) (m : S ⊗[R] N),
      ∀ r : ↥(I ^ n), 1 ⊗ₜ[R] l r = d r + (r : R) • m := by sorry

end LinearMap
