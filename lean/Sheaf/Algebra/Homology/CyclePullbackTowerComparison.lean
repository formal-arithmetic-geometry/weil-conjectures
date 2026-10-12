/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Algebra.Homology.CyclePullbackTower

/-! Pointwise comparisons for the explicit cycle-pullback tower. -/

@[expose] public section

universe v u vB uB
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.CyclePullback

/-- The pointwise pullback comparison and its first projection equation.
Source: Stacks Project, Derived Categories, Lemma 05T7 (1).
(blueprint: new-tower-comparison-first). -/
theorem tower_comparison_first {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    let d := (differential T π F N (i + 1)).app b
    let f := (F.obj b).d i (i + 1)
    let g := kernel.ι d ≫ (augmentation T π F N (i + 1)).app b
    ∃ (c : (term T π F N i).obj b ≅ T.obj (pullback f g)),
      c.hom ≫ π.app (pullback f g) ≫ pullback.fst f g =
        (augmentation T π F N i).app b := by sorry

/-- The second projection equation for the pointwise pullback comparison.
Source: Stacks Project, Derived Categories, Lemma 05T7 (1).
(blueprint: new-tower-comparison-second). -/
theorem tower_comparison_second {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N)
    (c : (term T π F N i).obj b ≅
      T.obj (pullback ((F.obj b).d i (i + 1))
        (kernel.ι ((differential T π F N (i + 1)).app b) ≫
          (augmentation T π F N (i + 1)).app b)))
    (h : c.hom ≫ π.app _ ≫ pullback.fst _ _ =
      (augmentation T π F N i).app b) :
    c.hom ≫ π.app _ ≫ pullback.snd _ _ ≫
      kernel.ι ((differential T π F N (i + 1)).app b) =
      (differential T π F N i).app b := by sorry


theorem tower_comparison {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    let d := (differential T π F N (i + 1)).app b
    let f := (F.obj b).d i (i + 1)
    let g := kernel.ι d ≫ (augmentation T π F N (i + 1)).app b
    ∃ (c : (term T π F N i).obj b ≅ T.obj (pullback f g)),
      c.hom ≫ π.app (pullback f g) ≫ pullback.fst f g =
        (augmentation T π F N i).app b ∧
      c.hom ≫ π.app (pullback f g) ≫ pullback.snd f g ≫ kernel.ι d =
        (differential T π F N i).app b := by
  dsimp
  obtain ⟨c, h₁⟩ := tower_comparison_first T π F N b i hi
  refine ⟨c, h₁, ?_⟩
  exact tower_comparison_second T π F N b i hi c h₁

end CochainComplex.CyclePullback
