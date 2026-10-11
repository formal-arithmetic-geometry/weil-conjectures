/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness of completion along a flat local map

Source: Stacks Project, More on Algebra, Lemma 0C4G (more-algebra-lemma-flat-completion),
line 10731, the implication from flatness of a local map to flatness of its completions
(blueprint: lem-weil-pbc-flat-completion).
-/

universe u v

/-- A flat local homomorphism of Noetherian local rings induces a flat homomorphism
on adic completions.

The map is characterized levelwise by the maps on quotients, and by compatibility
with the canonical maps.  Source: Stacks Project, More on Algebra, Lemma 0C4G,
line 10731 (blueprint: lem-weil-pbc-flat-completion).

Proof:
1. The canonical map from B to its completion is flat by
   `lem-weil-pbc-noetherian-completion-flat`. Compose it with the flat map φ using
   `lem-weil-pbc-flat-ring-map-comp` to make Bhat a flat A-module.
2. For every positive n, `lem-weil-pbc-flat-module-quotient-flat` makes
   Bhat / mA ^ n Bhat flat over A / mA ^ n.
3. By `lem-weil-pbc-local-completion-local-ring`, Ahat has maximal ideal mA Ahat,
   whose nth power is mA ^ n Ahat. By `lem-weil-pbc-adic-completion-mod-power`,
   the canonical map identifies A / mA ^ n with Ahat / (mA Ahat) ^ n;
   finite generation follows from `def-weil-pbc-noetherian-ring`.
4. The identity φhat.comp ιA = ιB.comp φ identifies (mA Ahat) ^ n Bhat with
   mA ^ n Bhat and their quotient module structures. Transport the flatness
   from step 2 along the ring isomorphism of step 3.
5. Both completions are Noetherian by `lem-weil-pbc-adic-completion-noetherian`.
   By `lem-weil-pbc-local-completion-local-ring`, Bhat is local with maximal
   ideal mB Bhat; locality of φ puts mA Bhat inside it. Bhat is finite over
   itself. Apply `lem-weil-pbc-flat-module-powers` with R = Ahat, I = mA Ahat,
   S = Bhat and M = S to conclude φhat.Flat (`def-weil-pbc-flat-ring-map`).
-/
theorem flat_adicCompletion_of_flat_local
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (hlocal : ∀ x : A, x ∈ IsLocalRing.maximalIdeal A →
      φ x ∈ IsLocalRing.maximalIdeal B) :
    let mA : Ideal A := IsLocalRing.maximalIdeal A
    let mB : Ideal B := IsLocalRing.maximalIdeal B
    let Ahat := AdicCompletion mA A
    let Bhat := AdicCompletion mB B
    let ιA : A →+* Ahat := algebraMap A Ahat
    let ιB : B →+* Bhat := algebraMap B Bhat
    ∃ φhat : Ahat →+* Bhat,
      (∀ n : ℕ,
        ((AdicCompletion.evalₐ mB n).toRingHom).comp φhat =
          (Ideal.Quotient.lift (mA ^ n)
            ((Ideal.Quotient.mk (mB ^ n)).comp φ) (by
              intro x hx
              change Ideal.Quotient.mk (mB ^ n) (φ x) = 0
              rw [Ideal.Quotient.eq_zero_iff_mem]
              exact (pow_le_pow_left' ((Ideal.map_le_iff_le_comap).2 (by
                intro y hy
                exact hlocal y hy)) n) (by
                  rw [← Ideal.map_pow]
                  exact Ideal.mem_map_of_mem φ hx)) ).comp
            (AdicCompletion.evalₐ mA n).toRingHom) ∧
      φhat.comp ιA = ιB.comp φ ∧ φhat.Flat := by
  sorry
