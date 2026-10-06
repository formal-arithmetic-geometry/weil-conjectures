/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic

/-!
# Geometrically irreducible constituents after a constant extension

A finite-dimensional representation `V` of the Weil group `W(C₀)` of a curve over `𝔽_q` need
not have geometrically irreducible constituents: an irreducible representation may split
under the geometric subgroup `π₁(C) = ker deg`. After a finite constant-field extension
`𝔽_{qᵐ}`, whose Weil group is the finite-index subgroup `deg⁻¹(mℤ)`, it does admit a filtration
whose graded pieces are irreducible under `π₁(C)`. This is the step of the Deligne–Laumon
reduction (blueprint subsection `sk-thm-dl-a1-upper`) reducing to geometrically irreducible
sheaves.

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_filtration_geometric_isIrreducible`: after passing to
  `deg⁻¹(mℤ)`, a finite-dimensional Weil representation has a filtration with nonzero
  geometrically irreducible graded pieces.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]

/-- *Geometrically irreducible constituents after a constant extension.* Let `ρ` be a
finite-dimensional `ℚ̄_ℓ`-representation of the Weil group `W(C₀)` of a curve `C₀` over `𝔽_q`.
There are `m > 0` and a finite filtration `0 = F₀ ⊂ F₁ ⊂ ⋯ ⊂ Fₙ = V` by subspaces stable
under the Weil group `deg⁻¹(mℤ)` of `C₀ ⊗ 𝔽_{qᵐ}`, whose graded pieces `Fᵢ₊₁ / Fᵢ` are nonzero
and irreducible under the geometric subgroup `π₁(C) = ker deg`.

By finite length it suffices to treat an irreducible `V`. Its restriction to the normal
subgroup `π₁(C)` is semisimple (Clifford), and a Frobenius lift permutes its finitely many
isotypic components; choose `m` killing this permutation. An irreducible summand of `V` under
`deg⁻¹(mℤ)` is then isotypic, `S ⊗ E` with `S` geometrically irreducible, and the Frobenius
acts as `T ⊗ B` by Schur's lemma; an eigenline of `B` gives a stable subspace `S ⊗ ⟨e⟩`, so
`dim E = 1`. Taking a common multiple of the degrees refines the filtration.

The blueprint states this for a lisse sheaf punctually `ι`-pure of weight `w`, and adds that the
graded pieces are pure of weight `w` too; this is automatic, since the local Frobenius
eigenvalues of a subquotient are among those of `V` (`lem-a1-subquotient-pure`), and neither
lissity nor purity enters the construction.
(blueprint: `lem-a1-geometric-constituent-reduction`) -/
theorem exists_filtration_geometric_isIrreducible
    (ρ : Representation (PadicAlgCl l) W.carrier V) :
    ∃ m : ℕ, 0 < m ∧ ∃ (n : ℕ) (F : Fin (n + 1) → Submodule (PadicAlgCl l) V),
      Monotone F ∧ F 0 = ⊥ ∧ F (Fin.last n) = ⊤ ∧
      (∀ (i : Fin (n + 1)) (g : W.carrier), (m : ℤ) ∣ Multiplicative.toAdd (W.deg g) →
        ∀ v ∈ F i, ρ g v ∈ F i) ∧
      ∀ i : Fin n, F i.castSucc < F i.succ ∧
        ∀ S : Submodule (PadicAlgCl l) V, F i.castSucc ≤ S → S ≤ F i.succ →
          (∀ g ∈ W.geometric, ∀ v ∈ S, ρ g v ∈ S) → S = F i.castSucc ∨ S = F i.succ :=
  sorry

end WeilGroup

end AlgebraicGeometry
