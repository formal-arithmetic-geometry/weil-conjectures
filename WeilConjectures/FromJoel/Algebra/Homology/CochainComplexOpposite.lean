/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite

/-!
# Quasi-isomorphisms and the opposite equivalence of cochain complexes

Supplement to `Mathlib.Algebra.Homology.CochainComplexOpposite`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.32.0`.

-/

@[expose] public section

open CategoryTheory Opposite

namespace CochainComplex

variable {C : Type*} [Category C] [Preadditive C]

lemma quasiIsoAt_opEquivalence_map_iff [CategoryWithHomology C]
    {K L : (CochainComplex C ℤ)ᵒᵖ} (f : K ⟶ L) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    QuasiIsoAt ((opEquivalence C).functor.map f) n ↔ QuasiIsoAt f.unop m := by
  obtain rfl : m = -n := by lia
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
    quasiIsoAt_iff' _ (-(n + 1)) (-n) (-(n - 1))
      (by simp only [prev]; lia) (by simp only [next]; lia)]
  rw [← ShortComplex.quasiIso_opMap_iff (C := C)]
  rfl

lemma quasiIso_opEquivalence_map_iff [CategoryWithHomology C]
    {K L : (CochainComplex C ℤ)ᵒᵖ} (f : K ⟶ L) :
    QuasiIso ((opEquivalence C).functor.map f) ↔ QuasiIso f.unop := by
  simp only [quasiIso_iff, fun n ↦ quasiIsoAt_opEquivalence_map_iff f n (-n)]
  exact ⟨fun hf i ↦ by convert hf (-i); simp, fun hf i ↦ hf _⟩

end CochainComplex
