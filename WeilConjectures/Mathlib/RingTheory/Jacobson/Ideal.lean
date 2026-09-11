/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Complements of ideals in the Jacobson radical

An ideal that together with an ideal contained in the Jacobson radical generates the unit
ideal is already the unit ideal (`Ideal.eq_top_of_sup_eq_top_of_le_jacobson`).
-/

@[expose] public section

/-- If an ideal contained in the Jacobson radical is a complement of `K`, then `K = ⊤`. -/
theorem Ideal.eq_top_of_sup_eq_top_of_le_jacobson {A : Type*} [CommRing A] {K I : Ideal A}
    (hI : I ≤ Ring.jacobson A) (h : K ⊔ I = ⊤) : K = ⊤ := by
  by_contra hK
  obtain ⟨M, hM, hKM⟩ := Ideal.exists_le_maximal K hK
  have hjac : Ring.jacobson A ≤ M := by
    rw [← Ideal.jacobson_bot, Ideal.jacobson]
    exact sInf_le ⟨bot_le, hM⟩
  exact hM.ne_top (top_le_iff.mp (h ▸ sup_le hKM (hI.trans hjac)))
