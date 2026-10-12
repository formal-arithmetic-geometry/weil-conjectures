/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.JapaneseDomain
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.CharP.Basic
import Sheaf.FieldTheory.NormalExtensionFixedField

/-!
# In characteristic p, N-2 is tested on finite purely inseparable extensions

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 032N
(blueprint: lem-weil-pbc-n2-char-p-purely-inseparable-criterion).

## Main statements

* `isN2_of_finite_purelyInseparable_integralClosure`: in positive characteristic,
  finiteness of integral closures in finite purely inseparable extensions implies N-2.
-/

@[expose] public section

universe u v

/-- In positive characteristic, a Noetherian domain is N-2 if its integral closure is
finite over it in every finite purely inseparable extension of its fraction field.
Source: Stacks Project, Algebra, Lemma Tag 032N (the `if` direction).
(blueprint: lem-weil-pbc-n2-char-p-purely-inseparable-criterion).

Proof (the six steps of the node, following Stacks Tag 032N):
1. Given a finite extension `L/K`, choose a finite normal extension `M/K` containing `L`
   (`lem-weil-pbc-finite-extension-in-finite-normal-extension`). The inclusion carries integral
   elements to integral elements by applying it to their monic equations. Thus the integral
   closure in `L` embeds as an `R`-submodule of that in `M`. Noetherianity reduces the claim
   to finiteness of the latter (`lem-weil-pbc-noetherian-submodule-finite`).
2. Split `M/K` through the fixed field `M_insep` of its automorphism group: `M_insep/K` is
   purely inseparable and `M/M_insep` separable
   (`lem-weil-pbc-normal-extension-purely-inseparable-then-galois`). Both extensions are finite:
   the intermediate field is a subspace of `M`, and a `K`-basis spans over `M_insep`.
   The hypothesis makes the integral closure `R'` of `R` in `M_insep` finite over `R`.
3. This finite algebra `R'` is Noetherian (`lem-weil-pbc-finite-algebra-noetherian`), and is a
   normal domain with fraction field `M_insep`
   (`lem-weil-pbc-integral-closure-finite-extension-normal`).
4. Apply `lem-weil-pbc-noetherian-normal-separable-integral-closure-finite` to `R'` and
   `M/M_insep`: its integral closure `R''` in `M` is finite over `R'`. It is finite over `R`
   by `lem-weil-pbc-finite-module-over-finite-algebra`.
5. The ring `R''` equals the integral closure of `R` in `M`. One inclusion follows from
   transitivity of integrality (`lem-weil-pbc-integral-transitive`); for the other, a monic
   equation over `R` is also a monic equation over `R'`. The `R`-module structures agree.
6. Step 1 now proves finiteness in every finite `L/K`, exactly `IsN2 R K`
   (`def-weil-pbc-japanese-domain`). -/
theorem isN2_of_finite_purelyInseparable_integralClosure
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (h : ∀ (L : Type v) [Field L] [Algebra K L] [Algebra R L]
      [IsScalarTower R K L] [FiniteDimensional K L] [IsPurelyInseparable K L],
      Module.Finite R (integralClosure R L)) :
    IsN2 R K := by
  sorry
