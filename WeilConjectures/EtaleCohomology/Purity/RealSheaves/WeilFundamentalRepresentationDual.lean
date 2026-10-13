/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation

/-!
# The Weil fundamental representation of the dual

For a lisse Weil sheaf `ℱ`, the evaluation pairing `(ℱ^∨)_t × ℱ_t → ℚ̄_ℓ` of the stalks at the
base point is perfect and invariant under the Weil fundamental representations, so the Weil
fundamental representation of the dual `ℱ^∨` is the contragredient of that of `ℱ`
(`AlgebraicGeometry.WeilGroup.nonempty_equiv_fundamentalRep_dual`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))]
  {W : WeilGroup (C ↘ Spec (.of K))}
  {M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber (AlgebraicClosure K)}
  {B : BasePointData W} (D : WeilMonodromyData B)

/-- **The Weil fundamental representation of the dual is the contragredient**: the evaluation
pairing of the stalks at the base point identifies the Weil fundamental representation of the
dual `ℱ^∨` of a lisse Weil sheaf with the dual of that of `ℱ`. -/
theorem nonempty_equiv_fundamentalRep_dual (F : WeilSheaf K l C) (hF : F.IsLisse) :
    Nonempty ((fundamentalRep M D (F.dual hF) hF.dual).Equiv (fundamentalRep M D F hF).dual) := by
  sorry

end AlgebraicGeometry.WeilGroup
