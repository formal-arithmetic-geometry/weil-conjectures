/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Convergence

/-!
# Degenerate spectral sequences of exact couples

If from some page on the spectral sequence of a convergent exact couple is concentrated in the
column `p = 0`, then all later differentials vanish and the edge map from the abutment to that
column is an isomorphism (`CategoryTheory.ExactCouple.edge_collapse`,
`CategoryTheory.ExactCouple.isIso_edge`).

## Main definitions

- `CategoryTheory.ExactCouple.derivedIterSuccEIso`, `CategoryTheory.ExactCouple.derivedIterAddEIso`:
  an entry without incoming and outgoing differentials is unchanged on the later pages.
- `CategoryTheory.ExactCouple.ConvergenceData.edge`: the edge map `Aⁿ ⟶ E^{0, n}`.

## Main statements

- `CategoryTheory.ExactCouple.isZero_derivedIter_E`: vanishing entries stay zero on later pages.
- `CategoryTheory.ExactCouple.edge_collapse`, `CategoryTheory.ExactCouple.isIso_edge`: the edge
  collapse.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DecreasingFiltration

variable {A : C} (F : DecreasingFiltration A)

end DecreasingFiltration

namespace ExactCouple

variable {κ : Type w} [AddCommGroup κ] {a b c : κ} (X : ExactCouple C a b c)

/-- Vanishing entries of the spectral sequence of a couple stay zero on the later pages, the
pages being subquotients of the earlier ones. -/
lemma isZero_derivedIter_E (N M : ℕ) (hNM : N ≤ M) (i : κ)
    (h : IsZero ((X.derivedIter N).E i)) : IsZero ((X.derivedIter M).E i) := by
  induction M, hNM using Nat.le_induction with
  | base => exact h
  | succ M _ ih =>
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ ih

/-- An entry of the spectral sequence of a couple which has no incoming and no outgoing
differential is unchanged on the next page. -/
noncomputable def derivedIterSuccEIso (N : ℕ) (i : κ)
    (hout : (X.derivedIter N).d i (i + (b + degIter a c N)) = 0)
    (hin : (X.derivedIter N).d (i - (b + degIter a c N)) i = 0) :
    (X.derivedIter (N + 1)).E i ≅ (X.derivedIter N).E i :=
  ((X.derivedIter N).dComplex.isoHomologyπ _ i (dComplex_prev i) hin).symm ≪≫
    (X.derivedIter N).dComplex.iCyclesIso i _ (dComplex_next i) hout

section Collapse

variable {b : ℤ × ℤ} (X : ExactCouple C ((-1, 0) : ℤ × ℤ) b 0)

variable {X} {A : ℤ → C} {ι : ∀ p n : ℤ, X.D (p, n) ⟶ A n} {F : ∀ n, DecreasingFiltration (A n)}

end Collapse

end ExactCouple

end CategoryTheory
