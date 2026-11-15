/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkUnitCancellation

/-!
# Minimal finite free complexes over a scheme stalk

## References

* Stacks Project, Tag 00MT
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded finite free complex over a stalk has a minimal homotopy representative
(Stacks, Tag 00MT). -/
theorem exists_stalk_minimal_complex {Y : Scheme.{u}} (y : Y)
    (P : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free
        (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin s)))) :
    ∃ Q : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ,
      Nonempty (HomotopyEquiv P Q) ∧ Q.IsStrictlyGE 0 ∧ Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ s : ℕ, Nonempty
        (Q.X n ≅ SheafOfModules.free
          (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin s)))) ∧
      ∀ a b : ℤ,
        (((Modules.pullback (Spec.map (Y.residue y))).mapHomologicalComplex _).obj
          Q).d a b = 0 := by
  classical
  choose n hn using hfree
  generalize hN : (∑ k ∈ Finset.range (d + 1), n (k : ℤ)) = N
  induction N using Nat.strong_induction_on generalizing P n with
  | h N ih =>
    by_cases hz : ∀ a b : ℤ,
        (((Modules.pullback (Spec.map (Y.residue y))).mapHomologicalComplex _).obj
          P).d a b = 0
    · exact ⟨P, ⟨HomotopyEquiv.refl P⟩, hge, hle, (fun j ↦ ⟨n j, hn j⟩), hz⟩
    · obtain ⟨P', n', i, hi, ⟨e⟩, hge', hle', hn', hni, hni1, hrest⟩ :=
        exists_stalk_unit_cancellation y P d hge hle n hn hz
      have hleRank : ∀ k : ℕ, n' (k : ℤ) ≤ n (k : ℤ) := by
        intro k
        by_cases hk : (k : ℤ) = (i : ℤ)
        · rw [hk]
          omega
        · by_cases hk1 : (k : ℤ) = (i : ℤ) + 1
          · rw [hk1]
            omega
          · rw [hrest (k : ℤ) hk hk1]
      have hlt : (∑ k ∈ Finset.range (d + 1), n' (k : ℤ)) < N := by
        rw [← hN]
        apply Finset.sum_lt_sum
        · intro k _
          exact hleRank k
        · exact ⟨i, Finset.mem_range.mpr (by omega), by omega⟩
      obtain ⟨Q, ⟨e'⟩, hQge, hQle, hQfree, hQzero⟩ :=
        ih _ hlt P' hge' hle' n' hn' rfl
      exact ⟨Q, ⟨e.trans e'⟩, hQge, hQle, hQfree, hQzero⟩

end AlgebraicGeometry.Scheme.Modules
