/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude

## Unfinished

`not_immediate_of_inertiaField` is `sorry`ed. Proved ingredients: Hensel's lemma for
Artin–Schreier and Kummer equations over the inertia field (`OhmGeneral/Hensel.lean`), the rank-one
approximation of `K(x)` by partial-fraction monomials (`OhmGeneral/PartialFractions.lean`), and
the residues of `K(x)` (`OhmGeneral/Residue.lean`). Missing: the residue field of the inertia
field is separable over `k(x̄)` (`isSeparable_residue_of_mem_inertiaField`, which rests on the
decomposition-field statement `exists_valuation_sub_lt_one_of_forall_decompositionSubgroup`),
i.e. decomposition/inertia theory for general valuation rings; the approximation of elements of
the inertia field (the henselisation lies in the completion only in rank one); and, in
mixed characteristic, a substitute for the discreteness used to terminate the Kummer normal form.
The case of `K` approximable by a discrete subfield is `GaussStability`.
-/
module

public import WeilConjectures.RingTheory.Valuation.ResidueSubfield
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Ohm's stability theorem, general form (statement)

Let `Ω` be a separably closed field with a valuation subring `𝒪`, `K ⊆ Ω` an algebraically closed
subfield and `x ∈ 𝒪` with residue transcendental over the residue field of `K`, so that the
valuation on `F = K(x)` is the Gauss valuation. Let `Lᵗ ⊆ Ω` be the inertia field of `𝒪` over `F`
(the fixed field of the inertia group). Then `Lᵗ` has no immediate extension of degree `p` inside
`Ω`: every such extension changes the residue field or the value group.
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

/-- The inertia field of `𝒪` over a subfield `F`: the fixed field of the inertia group. -/
noncomputable def inertiaField (F : Subfield Ω) : IntermediateField F Ω :=
  IntermediateField.fixedField ((𝒪.inertiaSubgroup F).map (𝒪.decompositionSubgroup F).subtype)

/-- **Ohm's stability theorem** (J. Ohm, *Simple transcendental extensions of valued fields*,
J. Math. Kyoto Univ. 22 (1982); F.-V. Kuhlmann, *Elimination of ramification I*, Trans. AMS 362
(2010), §4), in the form: the inertia field of `K(x)` with the Gauss valuation, `K` algebraically
closed, has no immediate extension of prime degree `p` (the residue characteristic). -/
theorem not_immediate_of_inertiaField [IsSepClosed Ω] {p : ℕ} [Fact p.Prime]
    [CharP (ResidueField 𝒪) p] (K : Subfield Ω) [IsAlgClosed K] {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    [Algebra.IsSeparable (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})) Ω]
    (M : Subfield Ω)
    (hLM : (𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}))).toSubfield ≤ M)
    (hdeg : Module.finrank (𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})))
      (M.toIntermediateField (K := 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪
        {(x : Ω)}))) fun c ↦ hLM c.2) = p) :
    ¬ (𝒪.residueSubfield M ≤
        𝒪.residueSubfield (𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪
          {(x : Ω)}))).toSubfield ∧
      ∀ z ∈ M, z ≠ 0 → ∃ y ∈ 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})),
        𝒪.valuation z = 𝒪.valuation y) := by
  sorry

end ValuationSubring
