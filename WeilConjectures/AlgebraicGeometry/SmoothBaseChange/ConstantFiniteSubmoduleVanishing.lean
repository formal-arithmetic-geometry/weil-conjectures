/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeColimit
import Mathlib.Algebra.Colimit.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Vanishing of constant coefficients from all finite submodules

Source: Stacks Project, Tag 0739, applied on affine etale objects; Tag 0F08, cyclic-coefficient
reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

-- Scalar restriction reduces finiteness to Mathlib's finite torsion Z-module theorem.
private theorem finite_fg_submodule
    (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) (n : ℕ) (hn : n ≠ 0)
    (hM : ∀ x : M, n • x = 0) (N : Submodule (ULift.{u + 1} ℤ) M)
    (hN : N.FG) : Finite N := by
  let : Module (ULift.{u + 1} ℤ) N := N.module
  have : Module.Finite ℤ (ULift.{u + 1} ℤ) := inferInstance
  have : Module.Finite (ULift.{u + 1} ℤ) N := Module.Finite.iff_fg.mpr hN
  have : Module.Finite ℤ N := Module.Finite.trans (ULift.{u + 1} ℤ) N
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast hn)⟩, ?_⟩
  apply Subtype.ext
  change (n : ℤ) • (x : M) = 0
  simpa using hM x

/-- Higher direct image of a constant bounded torsion module vanishes if it vanishes
for all finite submodules. The submodule index is allowed to live in the module's universe.

Source: Stacks Project, Tag 0739, and Tag 0F08, cyclic-coefficient reduction. -/
theorem isZero_higherDirectImage_constant_of_finite_submodules
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℤ) (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    (n : ℕ) (hn : n ≠ 0) (hM : ∀ x : M, n • x = 0)
    (hfinite : ∀ (N : Submodule (ULift.{u + 1} ℤ) M), Finite N →
      IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj
          (ModuleCat.of (ULift.{u + 1} ℤ) N)))) :
    IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj M)) :=
  by
    classical
    let R := ULift.{u + 1} ℤ
    let I := {N : Submodule R M // N.FG}
    have : Nonempty I := ⟨⟨⊥, Submodule.fg_bot⟩⟩
    let : ∀ N : I, Module R N.1 := fun N ↦ N.1.module
    let D := ModuleCat.directLimitDiagram (R := R) (fun N : I ↦ (N.1 : Type (u + 1)))
      (Module.fgSystem R M)
    let c := ModuleCat.directLimitCocone (R := R) (fun N : I ↦ (N.1 : Type (u + 1)))
      (Module.fgSystem R M)
    let H := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (lowerStar (ModuleCat.{u + 1} R) h).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ q
    have : PreservesColimitsOfShape I
        (DerivedCategory.Plus.singleFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) 0 ⋙
            (lowerStar (ModuleCat.{u + 1} R) h).rightDerivedFunctorPlus ⋙
              DerivedCategory.Plus.homologyFunctor _ q) :=
      preservesColimitsOfShape_higherDirectImage_large R h q I
    have : PreservesColimitsOfShape I H := by
      dsimp only [H, constantSheaf]
      infer_instance
    have hc : IsColimit c := ModuleCat.directLimitIsColimit _ _
    have hz : IsZero (H.obj c.pt) := (isColimitOfPreserves H hc).isZero_pt
      ((D ⋙ H).isZero (fun N ↦ by
        -- The hypothesis uses the canonical lifted-integer action on N.
        have hmodule : N.1.module = (ULift.module : Module R N.1) := by
          apply Module.ext
          funext r x
          have hr : (r.down : R) = r := by cases r; rfl
          rw [← hr]
          exact Int.cast_smul_eq_zsmul R r.down x
        have he : D.obj N = @ModuleCat.of R _ N.1 _ ULift.module := by
          change @ModuleCat.of R _ N.1 _ N.1.module = _
          rw [hmodule]
        change IsZero (H.obj (D.obj N))
        rw [he]
        exact hfinite N.1 (finite_fg_submodule M n hn hM N.1 N.2)))
    let e : c.pt ≅ M := (Module.fgSystem.equiv R M).toModuleIso
    exact hz.of_iso (H.mapIso e.symm)

end AlgebraicGeometry.Etale
