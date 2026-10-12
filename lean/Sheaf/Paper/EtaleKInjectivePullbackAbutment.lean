/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.EtaleTermwiseHypercohomology
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # K-injective computation of the étale pullback abutment

Source: Stacks Project, Tags 015J, 015K, 070I and 08BJ.
(blueprint: lem-weil-pbc-kinjective-pullback-abutment).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborating resolution and spectral-page comparison families together.
/-- A pullback comparison between K-injective resolutions computes the canonical
unit--Leray map, after the canonical resolution identifications.
Source: Stacks Project, Tag 015J (computation by an injective total resolution),
Tag 015K (independence of comparison maps), and Tags 070I and 08BJ
(K-injective comparison and direct image).
(blueprint: lem-weil-pbc-kinjective-pullback-abutment).

Proof: Apply the underived adjunction to the comparison j to obtain a map
I -> f_* J. Its composite with the resolution of K is homotopic to the
adjoint of v followed by the resolution of L. Pushforward preserves
K-injectives because its left adjoint is exact. Thus this adjoint comparison
computes the derived unit followed by Rf_*(v). Apply RΓ_X and the Leray
isomorphism RΓ_X Rf_* ≅ RΓ_Y. On K-injective complexes their defining units
are isomorphisms and naturality identifies the resulting map with Γ applied
to the adjoint comparison, or equivalently the degreewise unit followed by
Γ_Y(j). This is w by its component formula. Homotopic maps have equal maps
in the derived category. Finally apply H^n and the canonical resolution
isomorphisms; their factors are exactly resolutionEtaleCohomologyIso. -/
theorem etaleKInjective_pullback_abutment
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ L)
    (ρ : CochainComplex.KInjectiveResolutionChoice K)
    (σ : CochainComplex.KInjectiveResolutionChoice L)
    (j : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ρ.complex ⟶ σ.complex)
    (hj : Nonempty (Homotopy
      (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ρ.map ≫ j) (v ≫ σ.map)))
    (w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ρ.complex ⟶
        ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj σ.complex)
    (hw : ∀ i : ℤ, w.f i =
      globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (ρ.complex.X i) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (j.f i))
    (n : ℤ) :
    (@resolutionEtaleCohomologyIso.{uNatural} X K ρ.complex ρ.map
        ρ.quasiIso ρ.isKInjective n).inv ≫ HomologicalComplex.homologyMap w n ≫
      (@resolutionEtaleCohomologyIso.{uNatural} Y L σ.complex σ.map
        σ.quasiIso σ.isKInjective n).hom =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{uNatural + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
            ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app
              (DerivedCategory.Q.obj K)) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{uNatural + 1} f).hom.app
              ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj
                (DerivedCategory.Q.obj K)) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Y).map
            ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map v)) := by
  sorry

end AlgebraicGeometry.Etale
