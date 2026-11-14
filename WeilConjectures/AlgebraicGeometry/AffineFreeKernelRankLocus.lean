/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.AffineFreeMapZeroLocus
import WeilConjectures.AlgebraicGeometry.FreeKernelMaximalRankCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Limits

/-! # Closed maximal-rank kernel locus of a finite-free sheaf map

## References

* Stacks Project, Tags 0BDL and 0EWY
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A single map between finite-free sheaves on an affine scheme has a closed,
finitely presented locus representing rank-r locally free pulled-back kernels
when its domain has rank at most r. No complex or derived category is involved
(Stacks, Tags 0BDL and 0EWY). -/
theorem exists_affineFreeKernelRankLocus
    (X : Scheme.{u}) [IsAffine X]
    (M N : SheafOfModules.{u} (X.ringCatSheaf)) (d : M ⟶ N)
    (s n r : ℕ) (hsr : s ≤ r)
    (hM : Nonempty (M ≅ SheafOfModules.free
      (R := X.ringCatSheaf) (ULift.{u} (Fin s))))
    (hN : Nonempty (N ≅ SheafOfModules.free
      (R := X.ringCatSheaf) (ULift.{u} (Fin n)))) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
      IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ X),
        (∃ g : T ⟶ Z, g ≫ i = h) ↔
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            (kernel ((Modules.pullback h).map d)) r) := by
  classical
  have hframes (T : Scheme.{u}) (h : T ⟶ X) :
      Nonempty ((Modules.pullback h).obj M ≅ SheafOfModules.free
        (R := T.ringCatSheaf) (ULift.{u} (Fin s))) ∧
      Nonempty ((Modules.pullback h).obj N ≅ SheafOfModules.free
        (R := T.ringCatSheaf) (ULift.{u} (Fin n))) :=
    ⟨⟨(Modules.pullback h).mapIso hM.some ≪≫ Modules.pullbackFreeIso h _⟩,
      ⟨(Modules.pullback h).mapIso hN.some ≪≫ Modules.pullbackFreeIso h _⟩⟩
  have hcriterion (T : Scheme.{u}) (h : T ⟶ X) :=
    finiteLocallyFree_kernel_maximalRank_iff T _ _ ((Modules.pullback h).map d)
      s n r hsr (hframes T h).1 (hframes T h).2
  by_cases heq : s = r
  · obtain ⟨Z, i, hi, hfp, hZ⟩ := exists_affineFreeMapZeroLocus X M N d s n hM hN
    refine ⟨Z, i, hi, hfp, fun T h ↦ ?_⟩
    rw [hZ, hcriterion]
    simp only [heq, true_or, and_true]
  · refine ⟨∅, Scheme.emptyTo X, inferInstance, inferInstance, fun T h ↦ ?_⟩
    constructor
    · rintro ⟨g, _⟩
      have hempty : IsEmpty T := ⟨fun t ↦ isEmptyElim (g.base t)⟩
      apply (hcriterion T h).2
      exact ⟨(Modules.isZero_of_isEmpty
        ((Modules.pullback h).obj N)).eq_of_tgt _ _, Or.inr hempty⟩
    · intro hk
      have hempty : IsEmpty T := ((hcriterion T h).1 hk).2.resolve_left heq
      refine ⟨isInitialOfIsEmpty.to _, ?_⟩
      exact isInitialOfIsEmpty.hom_ext _ _

end AlgebraicGeometry.Scheme
