/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedSectionCompactOrigin.ClosedSectionCompactOriginData

/-! # Source normalization for a closed section

Source: Stacks Tags 0F7B and 0F7J.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ClosedSectionCompactOrigin

/-- The canonical compact-support comparison commutes with the prescribed source
identification for a closed section. This is only the source equation: it has no
class maps, target complexes, retained target comparison or bounded-below conclusion.

Source: Stacks Tags 0F7B and 0F7J. -/
theorem closedSectionSourceNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u}) {B X : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (f : X ⟶ B) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (s : B ⟶ X) [IsClosedImmersion s]
    [QuasiCompact s.openComplement.ι] (hs : s ≫ f = 𝟙 B) :
    (compactComparison P c (etaleSource P s)).hom ≫
        (ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).map (supportedComparison P s).hom ≫
        (proSigma P f c s hs).hom =
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (etaleSigma P f c s hs).hom) ≫
        (constantComparison P B).hom := by sorry

end AlgebraicGeometry.ClosedSectionCompactOrigin
