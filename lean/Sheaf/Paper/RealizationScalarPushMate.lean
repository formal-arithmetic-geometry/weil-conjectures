/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.RealizationScalarFunctor
public import Sheaf.Paper.CompletedTowerDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

/-! # Localization makes the normalized scalar direct-image mate invertible -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable {T U : Scheme.{u}} [IsNoetherian T] [IsNoetherian U]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
variable (h : T ⟶ U)
  (sT : RealizationScalarFunctorData l E T) (sU : RealizationScalarFunctorData l E U)

/-- The scalar-adjunction mate is invertible on every bounded-below complex.
Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 5.3(1).
(blueprint: lem-weil-pbc-realization-scalar-push-mate)

Proof: the completed coefficient isomorphism identifies scalar extension with
localization of continuous integral coefficients at l. The DVR equation
l = unit times a positive uniformizer power identifies it with the displayed
rational inclusion. Express restricted extension as the multiplication-by-l
sequence, with nth leg l^(-n) times the adjunction unit. Exact filtered colimits
compute each cohomology sheaf of this telescope. Choose a good truncation of a
representative of K below its bound; every stage has the same lower bound.
Qcqs direct-image continuity computes the pushed telescope by the same colimit.
The adjunct equation for b gives equality of the zeroth legs after restriction
and the canonical coefficient direct-image comparison. Additivity and
invertibility of l on the localized vertices give equality of every leg.
Colimit uniqueness makes the restricted b invertible on every cohomology
sheaf, hence in the derived category. Exact coefficient restriction reflects
isomorphisms, proving the assertion without constructibility or properness. -/
theorem realizationScalarPushMate_isIso [QuasiCompact h] [QuasiSeparated h]
    (cA : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (pbcAdicCompletion U (pbcIntegralDatum l E)) ≅
        pbcAdicCompletion T (pbcIntegralDatum l E))
    (hcA : cA.hom = completedCoefficientMap h (pbcIntegralDatum l E))
    (cE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l U E) ≅ rationalCoefficientSheaf l T E)
    (hcE : rationalCoefficientRestrictionNormalized l E h cE.hom)
    (sq : cA.hom ≫ (sT.integralIso.hom ≫ sT.inclusion) =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (sU.integralIso.hom ≫ sU.inclusion) ≫ cE.hom)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hK : DerivedCategory.TStructure.t.plus K)
    (b : (pbcDerivedExtend (sU.integralIso.hom ≫ sU.inclusion)).obj
        ((proEtaleRingDerivedDirectImage h _ _ cA).obj K) ⟶
      (proEtaleRingDerivedDirectImage h _ _ cE).obj
        ((pbcDerivedExtend (sT.integralIso.hom ≫ sT.inclusion)).obj K))
    (hb : (pbcDerivedScalarAdjunction (sU.integralIso.hom ≫ sU.inclusion)).homEquiv _ _ b =
      (proEtaleRingDerivedDirectImage h _ _ cA).map
        ((pbcDerivedScalarAdjunction (sT.integralIso.hom ≫ sT.inclusion)).unit.app K) ≫
      (proEtaleRingRestrictionDerivedDirectImage h
        (pbcAdicCompletion U (pbcIntegralDatum l E)) (rationalCoefficientSheaf l U E)
        (pbcAdicCompletion T (pbcIntegralDatum l E)) (rationalCoefficientSheaf l T E)
        (sU.integralIso.hom ≫ sU.inclusion) (sT.integralIso.hom ≫ sT.inclusion)
        cA cE sq).inv.app
          ((pbcDerivedExtend (sT.integralIso.hom ≫ sT.inclusion)).obj K)) :
    IsIso b := by
  sorry

end WeilConjectures
