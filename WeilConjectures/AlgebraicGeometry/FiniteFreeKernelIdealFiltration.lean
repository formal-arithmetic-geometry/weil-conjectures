/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.FiniteFreeKernelCoordinateStep
import Mathlib.Data.Fintype.Option

/-!
# Ideal quotients of a finite free kernel

## References

* Stacks Project, Tag 01XF
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A kernel inside a finite free module admits a finite chain starting at zero whose
successive quotients are quasi-coherent ideal sheaves. There is no cohomology hypothesis.
(Stacks, Tag 01XF.) -/
theorem finite_free_kernel_ideal_filtration (X : Scheme.{u})
    {I : Type u} [Finite I]
    (p : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    ∃ (n : ℕ) (F : ℕ → X.Modules),
      IsZero (F 0) ∧ Nonempty (F n ≅ kernel p) ∧
      ∀ j : ℕ, j < n → ∃ J : X.IdealSheafData,
        J.toModules.IsQuasicoherent ∧
        ∃ (a : F j ⟶ F (j + 1)) (b : F (j + 1) ⟶ J.toModules)
          (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  classical
  let P (I : Type u) : Prop :=
    ∀ p : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
        SheafOfModules.unit X.ringCatSheaf,
      ∃ (n : ℕ) (F : ℕ → X.Modules),
        IsZero (F 0) ∧ Nonempty (F n ≅ kernel p) ∧
        ∀ j : ℕ, j < n → ∃ J : X.IdealSheafData,
          J.toModules.IsQuasicoherent ∧
          ∃ (a : F j ⟶ F (j + 1)) (b : F (j + 1) ⟶ J.toModules)
            (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact
  have h : P I := by
    apply Finite.induction_empty_option (P := P)
    · intro A B e ih p
      let E := (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso e.toIso
      obtain ⟨n, F, hzero, ⟨hiso⟩, hsteps⟩ := ih (E.hom ≫ p)
      exact ⟨n, F, hzero, ⟨hiso ≪≫ kernelIsIsoComp E.hom p⟩, hsteps⟩
    · intro p
      have hz : IsZero (SheafOfModules.free (R := X.ringCatSheaf) PEmpty.{u + 1}) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan _)
        intro i
        exact PEmpty.elim i
      exact ⟨0, fun _ ↦ kernel p, (hz.of_mono (kernel.ι p)),
        ⟨Iso.refl _⟩, fun j hj ↦ (Nat.not_lt_zero j hj).elim⟩
    · intro A _ ih p
      let q := SheafOfModules.freeMap (R := X.ringCatSheaf) (some : A → Option A) ≫ p
      obtain ⟨n, F, hzero, ⟨e⟩, hsteps⟩ := ih q
      obtain ⟨J, hJ, a, b, w, hs⟩ := finite_free_kernel_coordinate_step X p
      let G : ℕ → X.Modules := fun j ↦ if j ≤ n then F j else kernel p
      have hG (j : ℕ) (hj : j ≤ n) : G j = F j := ite_eq_left hj
      have hGn : G (n + 1) = kernel p := ite_eq_right (by omega)
      refine ⟨n + 1, G, ?_, ?_, ?_⟩
      · rw [hG 0 (Nat.zero_le n)]
        exact hzero
      · rw [hGn]
        exact ⟨Iso.refl _⟩
      · intro j hj
        by_cases hjn : j < n
        · rw [hG j (by omega), hG (j + 1) (by omega)]
          exact hsteps j hjn
        · have heq : j = n := by omega
          subst j
          rw [hG n le_rfl, hGn]
          have w' : (e.hom ≫ a) ≫ b = 0 := by simp [Category.assoc, w]
          refine ⟨J, hJ, e.hom ≫ a, b, w', ?_⟩
          exact ShortComplex.shortExact_of_iso
            (ShortComplex.isoMk (S₁ := ShortComplex.mk a b w)
              (S₂ := ShortComplex.mk (e.hom ≫ a) b w') e.symm (Iso.refl _) (Iso.refl _)
              (by simp) (by simp)) hs
  exact h p

end AlgebraicGeometry
