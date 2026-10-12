/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.TensorPower

/-!
# Boundary stalks of middle extensions of lisse Weil sheaves

Let `j : U₀ ⟶ C₀` be a dense open immersion into a smooth curve over `k₀` and `F` a lisse Weil
sheaf on `U₀`. At a closed point `x` of `C₀` the stalk of the middle extension `j_* F` is the
module of inertia invariants of the geometric generic stalk `F_η̄`, Frobenius-equivariantly
(blueprint `lem-wf-boundary-stalk-invariants`). In particular, if `v` is an eigenvector of the
local Frobenius on `(j_* F)_x̄`, then `v ^ {⊗ k}` is an inertia invariant eigenvector of
`F^{⊗ k}`, so the `k`-th powers of the boundary eigenvalues of `j_* F` are boundary eigenvalues
of `j_* (F^{⊗ k})`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.hasEigenvalue_stalk_directImage_tensorPow`: powers of boundary
  eigenvalues are boundary eigenvalues of tensor powers.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Powers of boundary eigenvalues.** Let `j : U₀ ⟶ C₀` be a dense quasi-compact open
immersion into a smooth curve over `k₀`, `F` a lisse Weil sheaf on `U₀` and `x` a closed point
of `C₀`. If `α` is an eigenvalue of the local Frobenius on the stalk `(j_* F)_x̄`, then `α ^ k`
is an eigenvalue of the local Frobenius on `(j_* (F^{⊗ k}))_x̄` for every `k ≥ 1`.

By `lem-wf-boundary-stalk-invariants` the stalk `(j_* F)_x̄` is `F_η̄ ^ {I_x}` with the action of
a residue Frobenius lift; an eigenvector `v` has the inertia invariant eigenvector `v ^ {⊗ k}` in
`(F_η̄) ^ {⊗ k} = (F^{⊗ k})_η̄`. (blueprint: `lem-wf-boundary-semicontinuity`, Step 4) -/
theorem hasEigenvalue_stalk_directImage_tensorPow {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l U} (hF : F.IsLisse)
    (x : C.finitePoints) {α : PadicAlgCl l}
    (hα : (((directImage j).obj F).stalk x).frobeniusEnd.HasEigenvalue α) {k : ℕ}
    (hk : k ≠ 0) :
    (((directImage j).obj (F.tensorPow hF k)).stalk x).frobeniusEnd.HasEigenvalue (α ^ k) :=
  sorry

end AlgebraicGeometry.WeilSheaf
