/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransferAux

/-!
# Changing universes in the Brown representability criterion

Source: Stacks Project, Tag 0A8F, Lemma `lemma-brown`, with its set-indexing
convention made explicit (blueprint: lem-pc-brown-representability-universe-transfer).
-/

@[expose] public section

universe w v vH u

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

theorem brownCohomologicalRepresentabilityUniverseTransfer
    (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{max w v vH} C]
    (hC : IsCompactlyGeneratedTriangulated.{max w v vH} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) H)
    (hBrown : ∀ (A : Type u) [Category.{max w v vH} A]
      [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
      [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
      [IsTriangulated A] [HasCoproducts.{max w v vH} A],
      IsCompactlyGeneratedTriangulated.{max w v vH} A →
      ∀ (K : Aᵒᵖ ⥤ AddCommGrpCat.{max w v vH}) [K.IsHomological],
      (∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) K) →
      ∃ G : A, Nonempty (K ≅ preadditiveYoneda.obj G)) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  obtain ⟨G, hG⟩ := brownCohomologicalRepresentabilityUniverseTransfer_aux
    C hC H hH hBrown
  exact ⟨⟨G, hG⟩⟩

end CategoryTheory
