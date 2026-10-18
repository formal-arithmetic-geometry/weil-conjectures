/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ComparisonPullbackExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.OpenTensorNormalization

/-!
# Comparison preserves the canonical open tensor map

Source: Stacks Project, Tags 0GL1, 0E8I and 07A4; the finite-coefficient transport
paragraph of the blueprint proof of `thm-sf-pf-proetale`
(blueprint: lem-sf-comparison-open-tensor-coherence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison `A_U Lj_e^* ≅ Lj_p^* A_X`, with the exact derived
pullbacks identified with their total left derived functors. It is the degreewise
localization of the recorded section-normalized comparison, not a chosen isomorphism.
Source: Stacks Project, Tags 00WX and 0B65, and the blueprint finite-coefficient
transport paragraph (blueprint: lem-sf-comparison-open-tensor-coherence). -/
noncomputable def comparisonOpenDerivedPullbackIso
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) :
    L(Etale.upperStar (ModuleCat.{u + 1} Λ) j) ⋙
        D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U) ≅
      D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X) ⋙
        L(upperStar (ModuleCat.{u + 1} Λ) j) :=
  Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j)
      D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} Λ) j)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (F := Etale.upperStar (ModuleCat.{u + 1} Λ) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
      (G := comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙
        upperStar (ModuleCat.{u + 1} Λ) j)
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j) ≪≫
    Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      (upperStar (ModuleCat.{u + 1} Λ) j) ≪≫
    Functor.isoWhiskerLeft D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm

/-- The map `h_{K,N} = (1 ⊗ a_{j,N}) ∘ t_U` of the node. The tensor comparison is
that of the strong monoidal comparison pullback, computed on K-flat representatives;
`a` is the canonical comparison of pullbacks localized degreewise. These constructions
are natural in both inputs.
Source: Stacks Project, Tag 07A4, and the blueprint finite-coefficient transport
paragraph (blueprint: lem-sf-comparison-open-tensor-coherence). -/
noncomputable def comparisonOpenTensorIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    (K : Etale.DerivedCategoryModule Λ U) (N : Etale.DerivedCategoryModule Λ X) :
    D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) U).obj K).obj
          (L(Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj N)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K)).obj
          (L(upperStar (ModuleCat.{u + 1} Λ) j).obj
            (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj N)) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) K).app
        (L(Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj N) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
      (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K)).mapIso
        ((comparisonOpenDerivedPullbackIso Λ j).app N)

/-- The comparison carries the canonical etale open tensor map to the pro-etale
one, for arbitrary unbounded `K` and `N`, naturally in both variables. In diagrammatic
composition order the equality is `A_X(γe) ≫ e ≫ j_!(h) = t_X ≫ (e ⊗ 1) ≫ γp`.
Source: Stacks Project, Tags 0GL1, 0E8I and 07A4, and the finite-coefficient
transport paragraph of `thm-sf-pf-proetale`
(blueprint: lem-sf-comparison-open-tensor-coherence).

Proof plan:
1. Exactness of comparison pullback and both extensions by zero makes their termwise
   comparison descend to the unbounded derived localization. Use
   lem-sf-comparison-pullback-exact, lem-cbc-proetale-extension-zero-comparison,
   lem-weil-pbc-extension-by-zero-exact and lem-cbc-proetale-extension-zero.
2. The etale and pro-etale open tensor maps are the inverses of the respective
   adjunction projection isomorphisms (lem-pur-etale-open-derived-tensor and
   lem-cbc-extension-zero-projection-formula). By lem-sf-open-tensor-normalization
   they have the same unit/counit normalization, with identity open restriction.
3. Naturality of the tensor and restriction comparisons identifies `h` with the
   composite stated above (lem-weil-pbc-comparison-pullback and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
4. Choose flat-term K-flat representatives of `K` and `N`. The tensor comparison
   is the canonical pure-tensor comparison and the extension comparison is the
   termwise sheaf comparison. Both composites send a pure tensor to the extension
   of its first factor tensored with the restriction of its second factor.
   Check this on the open restriction and on complementary stalks, which vanish;
   the adjunction normalization and full faithfulness of extension by zero identify
   the sheaf maps. Naturality in the differentials gives equality of chain maps,
   and K-flat descent gives the displayed derived equality.
5. Every constituent is natural in both inputs. Only exactness, the canonical
   adjunctions and the canonical tensor comparisons were used, so no boundedness,
   constructibility, properness or finite Tor-amplitude hypothesis occurs. -/
theorem comparison_open_tensor_coherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule Λ U) (N : Etale.DerivedCategoryModule Λ X) :
    D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
        (((Etale.derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} Λ) j).inv.app K).app N) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) j).hom.app
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) U).obj K).obj
            (L(Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj N)) ≫
      D(openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).map
        (comparisonOpenTensorIso Λ j K N).hom =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ)
        (D(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj K)).hom.app N ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).hom.app K)).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj N) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} Λ) j).inv.app
        (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K)).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj N) := by
  sorry

end AlgebraicGeometry.ProEtale
