/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.AlgebraicGeometry.P1.P1CounitScalar

/-! # Equality of the chart and vector-trace shifted Tate coefficient maps

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-shifted-line-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  projectiveLineTraceDatum projectiveLineTraceTransport
  AlgebraicGeometry.Etale.purityScalarSingleMap
  WeilConjectures.PurityFiniteSetting.purityScalarUnitMap
  ExceptionalCoefficients.tensorIso ExceptionalCoefficients.unitIso
  singleFunctorObjUnitIso derivedTensorRightUnitor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  _root_.DerivedCategory.singleFunctors

private def normalizedCoefficientLine
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    FiniteSmoothPurity.CoefficientLineComparison φ N N hA hB T := by
  have hi := ProEtale.reductionTateOrdinaryScalar_isIso φ T N hA hB
  exact {
    roots := 𝟙 _
    roots_power := by simp only [Category.id_comp, Nat.div_self hN, one_nsmul]
    sheafIso := asIso (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
      (ProEtale.reductionEtaleTateMap φ T N hA hB))
    generators := by
      intro W a z
      simp only [asIso_hom, Equiv.apply_symm_apply]
      change (ProEtale.reductionEtaleTateMap φ T N hA hB).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
          Scheme.finiteEtaleTateOneGenerator B N T hB W (φ a) z
      simpa only [ProEtale.reductionEtaleTateMap] using
        (ProEtale.reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose_spec W a z
    derivedIso := ProEtale.reductionEtaleTateIso φ T N hA hB hT
    derived_normalization := Eq.refl
      (AlgebraicGeometry.Etale.purityScalarSingleMap φ T
          (Scheme.finiteEtaleTateLine T N A hA) ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map
          (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
            (ProEtale.reductionEtaleTateMap φ T N hA hB))) }

/-- Equality of the chart and vector-trace shifted Tate coefficient maps.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-shifted-line-scalar).

Proof: Construct coefficient-line comparison data from the actual ordinary Tate map: use the
identity root map and its proved generator formula; use the published derived Tate isomorphism
with its defining normalization.
The balancing uniqueness theorem identifies this sheaf map with the canonical vector-trace
balancing map. Expand the shift and single-functor scalar comparison and substitute that identity;
the remaining composites are definitionally identical. -/
theorem ordinaryChartShiftedLineScalarEq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (ProEtale.reductionEtaleShiftedLineIso φ T N hA hB hT).hom =
      VectorTraceScalar.line φ N hN hA hB T hT := by
  have hb := comparison_balancing_sheaf φ N hN hA hB T hT
    (normalizedCoefficientLine φ N hN hA hB T hT)
  change (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
    (ProEtale.reductionEtaleTateMap φ T N hA hB)) =
      (VectorTraceScalar.balancing φ N hN hA hB T hT 1).hom at hb
  dsimp only [ProEtale.reductionEtaleShiftedLineIso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, ProEtale.reductionEtaleTateIso, asIso_hom,
    ProEtale.reductionEtaleTateExtensionMap, VectorTraceScalar.line,
    WeilConjectures.PurityFiniteSetting.finiteTateScalarLineMap]
  simp only [Int.natCast_one]
  rw [hb]
  rfl

end AlgebraicGeometry.Etale
