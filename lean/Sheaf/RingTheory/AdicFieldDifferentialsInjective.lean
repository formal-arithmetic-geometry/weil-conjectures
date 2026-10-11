/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Algebra

/-!
# Base-field differentials of an adically formally smooth local algebra

Source: Stacks Project, More on Algebra, Theorem Tag 07EL, (2) implies (5),
and Proposition Tag 07NQ, final proof paragraph; Algebra, Proposition Tag 0322
(blueprint: lem-weil-pbc-fs-adic-field-differentials-injective).
-/

@[expose] public section

universe u v

namespace KaehlerDifferential

/-- Source: Stacks Project, Tags 07EL, 07NQ and 0322.
(blueprint: lem-weil-pbc-fs-adic-field-differentials-injective)
For a Noetherian local `k`-algebra `C` formally smooth for its maximal-ideal-adic topology,
the canonical map `K ⊗[k] Ω[k⁄ℤ] → K ⊗[C] Ω[C⁄ℤ]` is injective, where `K = C/m`.
The tensor factors are reversed from the printed statement via the canonical symmetry.
In characteristic zero its composition with the map to `Ω[K⁄ℤ]` is still injective.
In characteristic `p`, the canonical maps identify the differentials over `ℤ` and `ZMod p`.

Proof (the DAG's seven steps):
1. Since `C` is nonzero and `k` is a field, `k → C → K` embeds `k` in `K`, so their
characteristic is either zero or a prime. The displayed map is the residue-field base
change of the first map in the differential exact sequence for `ℤ → k → C`
(lem-weil-pbc-kahler-differentials-first-exact-sequence).
2. In characteristic zero, `K/k` is formally smooth
(lem-weil-pbc-char-zero-field-extension-formally-smooth). The first differential map
`K ⊗[k] Ω[k⁄ℤ] → Ω[K⁄ℤ]` is consequently injective by
lem-weil-pbc-formally-smooth-differentials-injective, following Tag 0322.
3. On generators, this map factors through `K ⊗[C] Ω[C⁄ℤ]` by the differential
exact-sequence map for `ℤ → C → K`. Injectivity of the composite proves both zero
characteristic conclusions.
4. In positive characteristic, adic formal smoothness gives geometric regularity
by lem-weil-pbc-fs-adic-field-geometrically-regular (07EL (2) implies (1)).
5. Geometric regularity gives injectivity of `H₁(L_{K/k}) → m/m²` by
lem-weil-pbc-geometrically-regular-h1-injective (07E5 (1) implies (3)).
6. This implies injectivity for differentials over the prime field by
lem-weil-pbc-h1-injective-differentials-injective-char-p (07E5 (3) implies (4)).
7. An integer-relative derivation kills the image of the prime field; thus the universal
properties identify differentials over `ℤ` and `ZMod p` for both `k` and `C`. These
identifications commute with the canonical map on differential generators. This gives
the asserted injectivity over `ℤ` and the positive-characteristic identifications. -/
theorem residueField_mapBaseChange_injective_of_formallySmoothAdic
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C]
    [IsLocalRing C] [IsNoetherianRing C]
    (h : Algebra.FormallySmoothAdic k C (IsLocalRing.maximalIdeal C)) :
    let K := IsLocalRing.ResidueField C
    let iota := ((mapBaseChange ℤ k C).baseChange K).comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k C K K
        (KaehlerDifferential ℤ k)).symm.toLinearMap
    Function.Injective iota ∧
      (∀ [CharZero k], Function.Injective ((mapBaseChange ℤ C K).comp iota)) ∧
      (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
        letI : CharP C p :=
          charP_of_injective_algebraMap (algebraMap k C).injective p
        letI := ZMod.algebra k p
        letI := ZMod.algebra C p
        Function.Bijective (map ℤ (ZMod p) k k) ∧
          Function.Bijective (map ℤ (ZMod p) C C)) := by
  sorry

end KaehlerDifferential
