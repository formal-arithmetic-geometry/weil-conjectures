/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.FiniteLength

/-!
# The dual of an irreducible lisse Weil sheaf

On a `k₀`-scheme with irreducible geometric fiber, the dual `M^∨` of an irreducible lisse Weil
sheaf `M` is irreducible lisse: a lisse subsheaf `N ⊆ M^∨` dualises to a lisse quotient
`M ≅ M^∨∨ ↠ N^∨`, whose kernel is a lisse subsheaf of `M`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.dual`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

/-- The dual of an irreducible lisse Weil sheaf is irreducible lisse. -/
theorem IsIrreducibleLisse.dual {M : WeilSheaf k₀ l X} (hM : M.IsIrreducibleLisse) :
    (M.dual hM.1).IsIrreducibleLisse :=
  sorry

end AlgebraicGeometry.WeilSheaf
