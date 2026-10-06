/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Total complexes of first quadrant double complexes

A double complex `K : HomologicalComplex₂ C (up ℕ) (up ℕ)` in a category with finite coproducts
has a total complex: the objects `K.X p q` with `p + q = n` form a finite family.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C]

instance hasTotal_up_nat (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    K.HasTotal (ComplexShape.up ℕ) := fun n ↦ by
  have : Finite ((ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)) ⁻¹' {n}) := by
    refine Set.Finite.to_subtype ((Set.finite_Iic (n, n)).subset ?_)
    rintro ⟨p, q⟩ (h : p + q = n)
    simp only [Set.mem_Iic, Prod.mk_le_mk]
    omega
  infer_instance

end HomologicalComplex₂
