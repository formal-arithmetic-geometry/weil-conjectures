/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDualPairing
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Pullback of duals of finite locally free modules

## References

* [Stacks, Tag 0FNV] (Modules, Example), [Stacks, Tag 01C8] (Modules, Lemma)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback commutes with duals of finite locally free modules.
(Stacks, Tags 0FNV, 01C8) -/
theorem nonempty_pullback_dual_iso_of_isFiniteLocallyFree
    {X S : Scheme.{u}} (e : S ⟶ X) (M : X.Modules) [M.IsFiniteLocallyFree] :
    Nonempty ((pullback e).obj (dual M) ≅ dual ((pullback e).obj M)) := by
  obtain ⟨p⟩ := nonempty_exactPairing_dual_of_isFiniteLocallyFree M
  let : ExactPairing (dual M) M := p
  let : ExactPairing ((pullback e).obj (dual M)) ((pullback e).obj M) :=
    ExactPairing.map (pullback e) (dual M) M
  exact ⟨(MonoidalClosed.ihomObjUnitIso
    ((pullback e).obj (dual M)) ((pullback e).obj M)).symm⟩

end AlgebraicGeometry.Scheme.Modules
