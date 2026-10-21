/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Finite subextensions of the p-adic algebraic closure

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-sfb-qlbar-condensed/det-def-sfb-qlbar-condensed-subextensions.md, clauses 1 and 2.
(blueprint: det-def-sfb-qlbar-condensed-subextensions).
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace PadicAlgCl

/-- Finite composita have the product degree bound, finite subextensions form a nonempty
directed poset, and every finite subset (hence every element) lies in a finite subextension.
Source: blueprint main-20261015, det-def-sfb-qlbar-condensed-subextensions, clauses 1 and 2.
(blueprint: det-def-sfb-qlbar-condensed-subextensions).

Proof: IntermediateField.finiteDimensional_sup and finrank_sup_le give the binary case,
with the lattice inclusions. Induct on the length of a finite family, splitting Fin (n+1)
into zero and successors. The empty supremum is the base field with degree one, and the
empty product is one. For the induction step apply the binary degree bound and the
induction hypothesis, and rewrite the product by Fin.prod_univ_succ. The bottom field
gives nonemptiness; the binary compositum gives the common upper bound. Each element of
the algebraic closure is integral. IntermediateField.finiteDimensional_adjoin applied to
a finite set therefore gives the actual finite field it generates; subset_adjoin puts
the set in it. Applying this to a singleton proves the union assertion. -/
theorem finiteSubextensions_directed (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (n : ℕ) (E : Fin n → FiniteIntermediateField ℓ),
      FiniteDimensional ℚ_[ℓ]
        (iSup (α := IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (fun i : Fin n ↦ (E i).1)) ∧
      (∀ i, (E i).1 ≤
        iSup (α := IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (fun j : Fin n ↦ (E j).1)) ∧
      Module.finrank ℚ_[ℓ]
        (iSup (α := IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (fun i : Fin n ↦ (E i).1)) ≤
          ∏ i, Module.finrank ℚ_[ℓ] ((E i).1)) ∧
    Nonempty (FiniteIntermediateField ℓ) ∧
    (∀ E F : FiniteIntermediateField ℓ, ∃ G : FiniteIntermediateField ℓ,
      E.1 ≤ G.1 ∧ F.1 ≤ G.1) ∧
    (∀ S : Finset (PadicAlgCl ℓ), ∃ E : FiniteIntermediateField ℓ,
      ∀ x, x ∈ S → x ∈ E.1) ∧
    (∀ x : PadicAlgCl ℓ, ∃ E : FiniteIntermediateField ℓ, x ∈ E.1) := by
  sorry

end PadicAlgCl
