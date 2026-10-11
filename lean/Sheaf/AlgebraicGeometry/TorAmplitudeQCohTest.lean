/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Testing Tor amplitude on quasi-coherent modules

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.10.6,
Tag 08EA, implication (2) implies (1) (blueprint: lem-pc-tor-amplitude-qcoh-test).
-/

universe uT wT

open CategoryTheory

namespace AlgebraicGeometry

/-- Quasi-coherent test modules detect the Tor amplitude of an object with
quasi-coherent cohomology on a quasi-separated scheme.
Source: Stacks Project, Tag 08EA (blueprint: lem-pc-tor-amplitude-qcoh-test).

Proof:
1. For an affine open `j : U → X`, quasi-separatedness makes `j` quasi-compact
   and separated. Pushforward preserves quasi-coherence (`pqf-lem-pushforward-qcoh`),
   and `j* j_* G = G`, so all quasi-coherent modules on `U` extend to `X`.
   Restriction is exact and commutes with derived tensor
   (`lem-pc-affine-derived-pullback-tensor-tilde`), so the assumed vanishing holds
   on `U` against every quasi-coherent module there.
   Exact restriction preserves quasi-coherence of the cohomology sheaves, so
   `E|U` lies in `D_QCoh(O_U)`.
2. Write `U = Spec A`. The affine derived equivalence
   (`lem-pc-affine-qcoh-derived-equivalence`) represents `E|U` by an A-module complex.
   The tensor/tilde comparison (`lem-pc-affine-derived-pullback-tensor-tilde`)
   and exactness and faithfulness of tilde give Tor amplitude `[a,b]` for that complex.
   The affine criterion (`lem-pc-affine-tor-amplitude-criterion`) gives vanishing
   against every O_U-module.
3. For any O_X-module, restriction of its derived tensor with `E` to every affine
   open has cohomology zero outside `[a,b]`. Restriction commutes with derived tensor
   by `lem-pc-affine-derived-pullback-tensor-tilde`. A sheaf zero on an affine open
   cover is zero, proving the required global vanishing. -/
theorem torAmplitude_of_quasiCoherent_tests (X : Scheme.{uT}) [QuasiSeparatedSpace X]
    [HasDerivedCategory.{wT} (SheafOfModules.{uT} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a b : ℤ) (hab : a ≤ b)
    (h : ∀ F : SheafOfModules.{uT} (moduleRings X.toRingedSpace),
      F.IsQuasicoherent → ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes X E F i) :
    ∀ G : SheafOfModules.{uT} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E G i := by
  sorry

end AlgebraicGeometry
