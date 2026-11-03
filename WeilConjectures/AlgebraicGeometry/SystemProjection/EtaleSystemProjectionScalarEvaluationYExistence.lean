/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionBasicData
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownLevelRealizationData
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

/-! # Target scalar evaluation comparison existence for normalized etale systems

Source: Zheng, Construction 4.1, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open scoped CategoryTheory.TwoSquare
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.Etale.SystemProjection

private def ordinaryComparison
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (G : A ⥤ B) (K : B ⥤ C) (H : D ⥤ E) (L : E ⥤ F)
    (R : A ⥤ D) (S : B ⥤ E) (T : C ⥤ F)
    (G02 : A ⥤ C) (H02 : D ⥤ F)
    (δ : R ⋙ H ≅ G ⋙ S) (κ : S ⋙ L ≅ K ⋙ T)
    (cg : G02 ≅ G ⋙ K) (ch : H02 ≅ H ⋙ L) : R ⋙ H02 ≅ G02 ⋙ T :=
  Functor.isoWhiskerLeft R ch ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight δ _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ κ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight cg.symm T

end AlgebraicGeometry.Etale.SystemProjection
