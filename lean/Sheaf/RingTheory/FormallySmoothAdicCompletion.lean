/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.RingTheory.FormallySmoothAdic
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Adic formal smoothness of the completion

Source: Stacks Project, More on Algebra, Lemma 15.38.4 (Tag 07ED), (1) implies (2)
with the base ring discrete (blueprint: lem-weil-pbc-fs-adic-completion).
-/

universe u v

namespace Algebra

/-- Formal smoothness for the `n`-adic topology passes to the completion when `n` is
finitely generated. The completion has its induced `R`-algebra structure, and its
ideal is the extension of `n` along the canonical map from `S`.
Source: Stacks Project, More on Algebra, Lemma 15.38.4 (Tag 07ED), (1) implies (2),
with the zero ideal on `R` (blueprint: lem-weil-pbc-fs-adic-completion).

Proof:
1. By `lem-weil-pbc-adic-completion-mod-power` (Stacks, Tag 05GG), the projections
   `pi_m : S^ → S/n^m` are surjective algebra maps, commute with the canonical
   `iota : S → S^`, and have kernel `n^m S^` for every positive `m`.
2. Expanding products of sums of generators proves `(n S^) ^ m = n^m S^`, so these
   kernels are precisely the powers of the extended ideal
   (`def-weil-pbc-algebra-hom-quotient`).
3. Given a square-zero ideal `J` of an `R`-algebra `D` and an algebra map
   `g : S^ → D/J` killing `(n S^) ^ k`, with `k` positive, restrict along `iota`.
   The map `g_0 = g ∘ iota` kills `n^k` (`def-weil-pbc-formally-smooth-adic`).
4. Formal smoothness of `S` provides a lift `f_0 : S → D` of `g_0`.
5. Since `f_0(n^k)` lies in `J` and `J^2 = 0`, `f_0` kills `n^(2k)`; this is the
   argument of Stacks Tag 07EC(1) using `def-weil-pbc-algebra-hom-quotient`.
6. Factor `f_0` through the quotient `S/n^(2k)` and compose with `pi_(2k)` to
   obtain the algebra map `f : S^ → D` extending `f_0`.
7. The map `g` also factors through `pi_(2k)`. Its factor and the reduction of
   the factor of `f_0` agree after the surjective quotient map from `S`, hence
   agree. Thus reduction of `f` is `g`, solving every required lifting problem.
-/
theorem FormallySmoothAdic.adicCompletion (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] (n : Ideal S) (hn : n.FG)
    (h : FormallySmoothAdic R S n) :
    FormallySmoothAdic R (AdicCompletion n S)
      (n.map (algebraMap S (AdicCompletion n S))) := by
  sorry

end Algebra
