/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel

/-! # Localization data preceding the Grothendieck Brown retract

Source: Stacks Project, Tag 0F5X, first paragraph.
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- Gabriel-Popescu localization followed by Brown representability on the module
category supplies a representation of the pullback of H.  Source: Stacks Project,
Tag 0F5X, `injectives-, first paragraph, and Tag 0F5V. -/
theorem grothendieckDerived_localization_brown_data
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w vA vH), PreservesLimitsOfShape (Discrete I) H) :
    ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (L : B ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ B)
        (adj : L ⊣ R), IsIso adj.counit ∧
        ∃ E : B, Nonempty (uliftYoneda.{vH}.obj E ≅
          L.op ⋙ H ⋙ forget AddCommGrpCat ⋙ uliftFunctor.{w}) := by
  obtain ⟨B, cB, zB, sB, pB, aB, tB, iB, sumsB, hB, L, R, adj, sL, hL, hc⟩ :=
    grothendieckDerived_compact_localization_model.{w, uA, vA, vH} (A := A)
  let := cB
  let := zB
  let := sB
  let := pB
  let := aB
  let := tB
  let := iB
  let := sumsB
  let := sL
  have := hL
  let K := L.op ⋙ H
  have : K.IsHomological := by dsimp [K]; infer_instance
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have hK : ∀ I : Type (max w vH), PreservesLimitsOfShape (Discrete I) K := by
    intro I
    have := hH (ULift.{max w vA vH} I)
    have : PreservesLimitsOfShape (Discrete I) H :=
      preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) H
    dsimp [K]
    infer_instance
  have hrep := brownCohomologicalRepresentabilityUniverseTransfer.{0} B hB K hK
  obtain ⟨E, ⟨rE⟩⟩ := hrep
  refine ⟨B, cB, L, R, adj, hc, E, ⟨?_⟩⟩
  exact (Functor.RepresentableBy.equivUliftYonedaIso _ E)
    (Functor.representableByUliftFunctorEquiv.symm rE)

end CategoryTheory
