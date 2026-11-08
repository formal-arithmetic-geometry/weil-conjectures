/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import Submission.WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Normalized derived tensor and projection comparison squares

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6
(blueprint: def-sfb-derived-projection-comparison-squares).

These predicates expand the tensor, localization and adjunction-transpose squares.
They impose equations on the specified comparisons, without choosing maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
universe a b c e ha hb hc he wa wb wt
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.ConstantModuleDerivedProjection

/-- The square for four specified tensor comparisons.
Source: Stacks Tag 07A4
(blueprint: def-sfb-derived-projection-comparison-squares). -/
def TensorSquare
    {B : Type a} {E : Type b} {F : Type c} {H : Type e}
    [Category.{ha} B] [Category.{hb} E] [Category.{hc} F] [Category.{he} H]
    [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory F] [MonoidalCategory H]
    (L : B ⥤ E) (L' : F ⥤ H) (S : B ⥤ F) (T : E ⥤ H)
    (mL : L.Monoidal) (mL' : L'.Monoidal) (mS : S.Monoidal) (mT : T.Monoidal)
    (i : L ⋙ T ≅ S ⋙ L') : Prop :=
  letI := mL
  letI := mL'
  letI := mS
  letI := mT
  ∀ X Y : B,
    T.map (Functor.OplaxMonoidal.δ L X Y) ≫
      Functor.OplaxMonoidal.δ T (L.obj X) (L.obj Y) ≫ (i.hom.app X ⊗ₘ i.hom.app Y) =
    i.hom.app (X ⊗ Y) ≫ L'.map (Functor.OplaxMonoidal.δ S X Y) ≫
      Functor.OplaxMonoidal.δ L' (S.obj X) (S.obj Y)

/-- A full adjunction comparison under two functors, including unit and counit.
Source: Stacks Tag 07A6
(blueprint: def-sfb-derived-projection-comparison-squares). -/
def AdjunctionSquare
    {B : Type a} {E : Type b} {F : Type c} {H : Type e}
    [Category.{ha} B] [Category.{hb} E] [Category.{hc} F] [Category.{he} H]
    (L : B ⥤ E) (R : E ⥤ B) (L' : F ⥤ H) (R' : H ⥤ F)
    (adj : L ⊣ R) (adj' : L' ⊣ R') (S : B ⥤ F) (T : E ⥤ H)
    (i : L ⋙ T ≅ S ⋙ L') (j : R ⋙ S ≅ T ⋙ R') : Prop :=
  (∀ (M : B) (N : E) (f : L.obj M ⟶ N),
    adj'.homEquiv _ _ (i.inv.app M ≫ T.map f) =
      S.map (adj.homEquiv M N f) ≫ j.hom.app N) ∧
  (∀ M : B, S.map (adj.unit.app M) ≫ j.hom.app (L.obj M) ≫
    R'.map (i.hom.app M) = adj'.unit.app (S.obj M)) ∧
  (∀ N : E, T.map (adj.counit.app N) = i.hom.app (R.obj N) ≫
    L'.map (j.hom.app N) ≫ adj'.counit.app (T.obj N))

/-- Equality of the two specified adjunction transposes after scalar restriction.
Source: Stacks Tag 07A6
(blueprint: def-sfb-derived-projection-comparison-squares). -/
def ProjectionSquare
    {B : Type a} {E : Type b} {F : Type c} {H : Type e}
    [Category.{ha} B] [Category.{hb} E] [Category.{hc} F] [Category.{he} H]
    [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory F] [MonoidalCategory H]
    (L : B ⥤ E) (R : E ⥤ B) (L' : F ⥤ H) (R' : H ⥤ F)
    (adj : L ⊣ R) (adj' : L' ⊣ R') (S : B ⥤ F) (T : E ⥤ H)
    (mL : L.Monoidal) (mL' : L'.Monoidal) (mS : S.Monoidal) (mT : T.Monoidal)
    (i : L ⋙ T ≅ S ⋙ L') (j : R ⋙ S ≅ T ⋙ R') : Prop :=
  letI := mL
  letI := mL'
  letI := mS
  letI := mT
  ∀ (X : E) (Y : B),
    S.map (((adj.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans L)).app X).app Y) ≫
      j.hom.app (X ⊗ L.obj Y) ≫
      R'.map (Functor.OplaxMonoidal.δ T X (L.obj Y) ≫ (𝟙 _ ⊗ₘ i.hom.app Y)) =
    Functor.OplaxMonoidal.δ S (R.obj X) Y ≫ (j.hom.app X ⊗ₘ 𝟙 _) ≫
      ((adj'.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans L')).app
        (T.obj X)).app (S.obj Y)

/-- Normalized tensor and adjunction comparisons, retaining their projection mate square.
Source: Stacks Tags 07A4 and 07A6
(blueprint: def-sfb-derived-projection-comparison-squares). -/
structure NormalizedComparison
    {B : Type a} {E : Type b} {F : Type c} {H : Type e}
    [Category.{ha} B] [Category.{hb} E] [Category.{hc} F] [Category.{he} H]
    [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory F] [MonoidalCategory H]
    (L : B ⥤ E) (R : E ⥤ B) (L' : F ⥤ H) (R' : H ⥤ F)
    (adj : L ⊣ R) (adj' : L' ⊣ R') (S : B ⥤ F) (T : E ⥤ H)
    (mS : S.Monoidal) (mT : T.Monoidal)
    (leftNorm : (L ⋙ T ≅ S ⋙ L') → Prop)
    (rightNorm : (R ⋙ S ≅ T ⋙ R') → Prop)
    (Tensor : (L ⋙ T ≅ S ⋙ L') → Type wt)
    (tensorL : ∀ i, Tensor i → L.Monoidal)
    (tensorL' : ∀ i, Tensor i → L'.Monoidal) where
  left : L ⋙ T ≅ S ⋙ L'
  right : R ⋙ S ≅ T ⋙ R'
  tensor : Tensor left
  left_normalized : leftNorm left
  right_normalized : rightNorm right
  tensor_square : TensorSquare L L' S T
    (tensorL left tensor) (tensorL' left tensor) mS mT left
  adjunction : AdjunctionSquare L R L' R' adj adj' S T left right
  projection : ProjectionSquare L R L' R' adj adj' S T
    (tensorL left tensor) (tensorL' left tensor) mS mT left right

end CategoryTheory.ConstantModuleDerivedProjection
