/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ExtPullbackHomComplex
public import Sheaf.Paper.EtaleCETotalSections
public import Sheaf.AlgebraicGeometry.SheafHExtResolutionSectionsIso
import Sheaf.AlgebraicGeometry.ConstantSheafPullbackTranspose

/-! # Evaluation square for integer-indexed sections

Source: Stacks Project, Tags 015K, 01F9 and 01FA.
(blueprint: lem-weil-pbc-row-sections-evaluation-square).
-/
@[expose] public section
universe uNatural
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex Abelian
namespace AlgebraicGeometry.Etale
open Scheme

/-- Evaluation of the integer Hom complex commutes with pullback and sections.
Source: Stacks Project, Tags 015K, 01F9 and 01FA.
(blueprint: lem-weil-pbc-row-sections-evaluation-square).

Proof. Set L = f inverse image and α equal to the inverse constant-sheaf
comparison. Expand complexSectionsIso in degree n on an arbitrary cochain a.
The inverse fromSingleEquiv converts it into a morphism from the constant integer
sheaf into K in degree n. The definition of homPullbackMap sends it to
fromSingleMk (α;L(fromSingleEquiv a);ψ in degree n). Applying evaluation cancels
fromSingleMk with fromSingleEquiv. Naturality of the adjunction hom equivalence
then moves postcomposition by ψ outside sectionsEquiv. The constant-sheaf
pullback transpose identifies evaluation of α;L(fromSingleEquiv a) with the
adjunction unit on global sections. Naturality of ΓNatIsoSheafSections and the
formula for lowerStarCompGlobalSectionsIso identify this unit with ceSectionsUnit.
Thus both sides have the same value on every degree-n cochain. Extensionality
of group morphisms and complex maps gives the square. Nothing here uses
injectivity, a resolution augmentation, or a nonnegative degree. Zero complexes,
zero maps, negative degrees and empty schemes obey the same component formulas. -/
theorem ceComplexSectionsSquare {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    {K' : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    (ψ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (.up ℤ)).obj K ⟶ K') :
    SheafPullbackResolution.homPullbackMap (upperStar AddCommGrpCat.{uNatural + 1} f)
        ((upperStarConstantSheafIso AddCommGrpCat.{uNatural + 1} f).inv.app
          (AddCommGrpCat.of (ULift.{uNatural + 1} ℤ))) K K' ψ ≫
        (SheafPullbackResolution.complexSectionsIso Y K').hom =
      (SheafPullbackResolution.complexSectionsIso X K).hom ≫
        ((NatTrans.mapHomologicalComplex (ceSectionsUnit f) (.up ℤ)).app K ≫
          ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
            (.up ℤ)).map ψ) := by sorry

end AlgebraicGeometry.Etale
