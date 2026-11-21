/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
import WeilConjectures.CategoryTheory.DerivedShiftedFreeCoproduct
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A derived module object has an exhaustive cellular filtration of a representative.
Source: Stacks Project, More on Algebra, Remark 15.60.11 (Tag 09PB), and
Differential Graded Algebra, Lemma 22.20.4 (Tag 09KP). -/
theorem derivedModuleCellularFiltration (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    ∃ (L : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (F : ℕ → CochainComplex (ModuleCat.{max u v} R) ℤ)
      (ι : ∀ n, F n ⟶ L) (step : ∀ n, F n ⟶ F (n + 1)),
      Nonempty (K ≅ DerivedCategory.Q.obj L) ∧
      IsZero (DerivedCategory.Q.obj (F 0)) ∧
      (∀ n, Mono (ι n)) ∧
      (∀ n, step n ≫ ι (n + 1) = ι n) ∧
      (∀ (k : ℤ) (x : L.X k), ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x) ∧
      (∀ n, ∃ (I : Type (max u v)) (degree : I → ℤ)
        (G : DerivedCategory (ModuleCat.{max u v} R))
        (j : ∀ i : I, (((DerivedCategory.singleFunctor
          (ModuleCat.{max u v} R) 0).obj (ModuleCat.of R (ULift.{v} R)))⟦degree i⟧) ⟶ G),
        Nonempty (IsColimit (Cofan.mk G j)) ∧
        ∃ (a : G ⟶ DerivedCategory.Q.obj (F n))
          (b : DerivedCategory.Q.obj (F n) ⟶ DerivedCategory.Q.obj (F (n + 1)))
          (c : DerivedCategory.Q.obj (F (n + 1)) ⟶ G⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk a b c ∈ Pretriangulated.distinguishedTriangles) := by
  classical
  let M := DerivedCategory.Q.objPreimage K
  obtain ⟨L, q, hq, F, ι, step, hzero, hmono, hcompat, hexhaustive, hsplit, hquot⟩ :=
    CochainComplex.exists_large_filtered_free_resolution M
  let : QuasiIso q := hq
  refine ⟨L, F, ι, step, ?_, DerivedCategory.Q.map_isZero hzero,
    hmono, hcompat, hexhaustive, ?_⟩
  · exact ⟨(DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map q)).symm⟩
  · intro n
    let : Mono (ι n) := hmono n
    let : Mono (step n) := mono_of_mono_fac (hcompat n)
    obtain ⟨I, degree, he⟩ := hquot n
    obtain ⟨d, j, hc⟩ := derivedShiftedFreeCoproduct R (cokernel (step n)) I degree he
    let S := ShortComplex.mk (step n) (cokernel.π (step n)) (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (step n) }
    let T := (DerivedCategory.triangleOfSES hS).invRotate
    refine ⟨I, d, T.obj₁, j, hc, T.mor₁, T.mor₂, T.mor₃, ?_⟩
    exact Pretriangulated.inv_rot_of_distTriang _
      (DerivedCategory.triangleOfSES_distinguished hS)

end CategoryTheory
