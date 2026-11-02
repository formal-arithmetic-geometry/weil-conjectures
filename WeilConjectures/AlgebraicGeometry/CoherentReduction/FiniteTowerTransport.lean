/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentMappingSystems
public import WeilConjectures.AlgebraicGeometry.FiniteProperQuotient.FiniteExceptionalDerivedHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarPullbackMateInverseNormalized
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Canonical finite evaluation of coherent mapping systems
Source: Zheng 4.1, 5.16, 5.22; Stacks 03CY, 06YT, 08J9 and 0D6E.
(blueprint: def-sfb-coherent-hom-evaluation-transport).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.CoherentReduction
attribute [local instance] proEtSmall sequenceSmall
variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The coefficient-sized localization used by finite global sections.
Source: Stacks 079D (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
local instance scalarSmallDerived (A : Type (u + 1)) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- Ordinary restriction from A_n to O with the original quotient action.
Source: Stacks 06YY (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def finiteScalarRestriction (n : ℕ) :=
  ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (quotient l E n)

/-- Ordinary scalar restriction preserves addition of morphisms.
Source: Stacks 06YY (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
instance finiteScalarRestriction_additive (n : ℕ) :
    (finiteScalarRestriction l E n).Additive := by
  unfold finiteScalarRestriction
  infer_instance

/-- Restriction preserves finite limits, using the explicitly sized scalar adjunction.
Source: Stacks 06YY (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
instance finiteScalarRestriction_limits (n : ℕ) :
    PreservesFiniteLimits (finiteScalarRestriction l E n) := by
  let : PreservesLimitsOfSize.{0, 0} (finiteScalarRestriction l E n) :=
    (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
      (quotient l E n)).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize0.preservesFiniteLimits _

/-- Restriction preserves finite colimits, using the explicitly sized coextension adjunction.
Source: Stacks 06YY (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
instance finiteScalarRestriction_colimits (n : ℕ) :
    PreservesFiniteColimits (finiteScalarRestriction l E n) := by
  let : PreservesColimitsOfSize.{0, 0} (finiteScalarRestriction l E n) :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, u + 1, u + 1}
      (quotient l E n)).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize0.preservesFiniteColimits _

/-- Derived restriction in the coefficient-sized localizations of finite global sections.
Source: Stacks 06YY (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def finiteScalarRestrictionD (n : ℕ) :
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
  (finiteScalarRestriction l E n).mapDerivedCategory

/-- Exact O-valued evaluation, with no scalar forgetting.
Source: Zheng 4.1 (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def scalarEvaluation (n : ℕ) :=
  (CategoryTheory.evaluation ℕᵒᵖ
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj (op n)

/-- Exactness of evaluation of scalar towers.
Source: Stacks 0941 (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
instance scalarEvaluation_additive (n : ℕ) : (scalarEvaluation l E n).Additive := by
  unfold scalarEvaluation
  infer_instance

/-- Evaluation preserves finite limits.
Source: Stacks 0941 (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
instance scalarEvaluation_limits (n : ℕ) : PreservesFiniteLimits (scalarEvaluation l E n) := by
  unfold scalarEvaluation
  infer_instance

/-- Evaluation preserves finite colimits.
Source: Stacks 0941 (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
instance scalarEvaluation_colimits (n : ℕ) : PreservesFiniteColimits (scalarEvaluation l E n) := by
  unfold scalarEvaluation
  infer_instance

/-- The existing system Grothendieck structure, required by the derived-section maps.
Source: Zheng 4.1 (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
local instance systemGrothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X)) :=
  (calculus l E X).grothendieck

/-- O-valued sections of a level module in its fixed finite-coefficient presentation.
Source: Stacks 0B6E (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def finiteSections (X : Scheme.{u}) (n : ℕ) :=
  finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n) ⋙
    globalSectionsFunctor (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) X ⋙
      finiteScalarRestriction l E n

/-- Additivity of finite O-linear sections.
Source: Stacks 0B6E (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
instance finiteSections_additive (X : Scheme.{u}) (n : ℕ) :
    (finiteSections l E X n).Additive := by
  unfold finiteSections
  infer_instance

/-- The vertical O-module presheaf at n, before taking its limit.
Source: Stacks 0B6E (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def scalarVertical (X : Scheme.{u}) (n : ℕ)
    (M : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X)) :=
  (Functor.curry.obj ((prodOpEquiv (C := ℕ) (D := X.ProEt)).inverse ⋙
    systemRestrictionObj (Scheme.ProEt.topology X) (coefficients l E X)
      (transitions l E X) (Padic.coefficientExtensionIntegers l E)
      (scalarAlgebra l E X) M)).obj (op n)

set_option maxHeartbeats 1600000 in
-- Comparing the two explicit section-module actions requires expanding their presentations.
set_option maxHeartbeats 1600000 in
-- Expanding the vertical limit and its two scalar actions is expensive.
section DerivedComparison
universe a b c va vb vc da db dc
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{da} A] [HasDerivedCategory.{db} B] [HasDerivedCategory.{dc} C]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (R : B ⥤ C) [R.Additive]
/-- The canonical comparison R(LR)→D(L)R(R), before claiming invertibility.
Source: Stacks 0D6E (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def exactRightDerivedComparison :
    (L ⋙ R).rightDerivedFunctor ⟶ L.mapDerivedCategory ⋙ R.rightDerivedFunctor :=
  (L ⋙ R).rightDerivedFunctor.rightDerivedDesc (L ⋙ R).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso A (.up ℤ)) _
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit L R)
end DerivedComparison

/-- The derived terminal-section presentation of the published global-section functor.
Source: Stacks 0B6E (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def finiteGlobalSectionsComparison (X : Scheme.{u}) (n : ℕ) :
    (globalSectionsFunctor
      (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) X).rightDerivedFunctor ≅
      rightDerivedGlobalSections
        (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) X :=
  Functor.rightDerivedFunctorNatIso
    (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n))
      (Scheme.ProEt.isTerminalMkId X)).symm

set_option maxHeartbeats 1600000 in
-- The exact-presentation and section-localization functors have large inferred types.
/-- Factor finite O-sections through the fixed coefficient presentation and RΓ.
Source: Stacks 0D6E (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def fixedSectionsComparison (X : Scheme.{u}) (n : ℕ) :
    (finiteSections l E X n).rightDerivedFunctor ⟶
      (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory ⋙
        rightDerivedGlobalSections
          (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) X ⋙
        finiteScalarRestrictionD l E n :=
  exactRightDerivedComparison
    (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n))
    (globalSectionsFunctor (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) X ⋙
      finiteScalarRestriction l E n) ≫
    Functor.whiskerLeft
      (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (globalSectionsFunctor (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) X)
        (finiteScalarRestriction l E n)).hom ≫
    Functor.whiskerLeft
      (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory
      (Functor.whiskerRight (finiteGlobalSectionsComparison l E X n).hom
        (finiteScalarRestrictionD l E n))

/-- K-flat representatives with their localization isomorphism, chosen from the proved
resolution theorem, rather than from an existence of comparison maps.
Source: Stacks 06YN (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
structure FlatPresentation (X : Scheme.{u}) (n : ℕ)
    (M : D (Scheme.ProEt.topology X) (coefficients l E X n)) where
  complex : CochainComplex (Mod (Scheme.ProEt.topology X) (coefficients l E X n)) ℤ
  flat : complex.IsKFlatIndependentCoefficients
  iso : DerivedCategory.Q.obj complex ≅ M

/-- A genuine K-flat resolution of the specified object.
Source: Stacks 06YN (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def flatPresentation (X : Scheme.{u}) (n : ℕ)
    (M : D (Scheme.ProEt.topology X) (coefficients l E X n)) :
    FlatPresentation l E X n M := by
  let h := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (R := coefficients l E X n) (DerivedCategory.Q.objPreimage M)
  let P := h.choose
  let f := h.choose_spec.choose
  have hP := h.choose_spec.choose_spec
  letI := hP.2.2.1
  exact ⟨P, hP.1, asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩

/-- Tensor localization is invertible on these exact monoidal images of K-flat complexes.
Source: Stacks 06YT (blueprint: def-sfb-coherent-hom-evaluation-transport).
Proof: finiteUnrealization is an exact monoidal equivalence; its inverse takes
acyclic tests to acyclic tests, hence its termwise image preserves K-flatness.
The native localization tensorator on a K-flat pair is therefore invertible. -/
theorem fixedTensorLocalization_isIso (X : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (Mod (Scheme.ProEt.topology X) (coefficients l E X n)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients) :
    letI := finiteUnrealizationMonoidal X (Etale.FiniteProperQuotient.Ring l E n)
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      (((finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapHomologicalComplex
        (.up ℤ)).obj P)
      (((finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapHomologicalComplex
        (.up ℤ)).obj Q)) := by
  sorry

/-- The actual tensor transport: resolve, use the recorded tensor model, apply the
ordinary pure-tensor comparison, and undo the target localization tensorator.
Source: Stacks 06YT (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def fixedTensorComparison (X : Scheme.{u}) (n : ℕ)
    (M N : D (Scheme.ProEt.topology X) (coefficients l E X n)) :
    (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory.obj
      ((calculus l E X).levelClosed n |>.tensor.obj (M, N)) ≅
    (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory.obj M ⊗
      (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory.obj N := by
  let U := finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)
  letI := finiteUnrealizationMonoidal X (Etale.FiniteProperQuotient.Ring l E n)
  let P := flatPresentation l E X n M
  let Q := flatPresentation l E X n N
  letI := fixedTensorLocalization_isIso l E X n P.complex Q.complex P.flat Q.flat
  exact U.mapDerivedCategory.mapIso
      (((calculus l E X).levelClosed n).tensor.mapIso (P.iso.symm.prod Q.iso.symm)) ≪≫
    U.mapDerivedCategory.mapIso
      (CoefficientTensorModels.iso _ _ _ ((calculus l E X).levelTensorModels n)
        P.complex Q.complex P.flat Q.flat).symm ≪≫
    U.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (Functor.mapCochainComplexμIso U P.complex Q.complex).symm ≪≫
    (asIso (Functor.LaxMonoidal.μ DerivedCategory.Q _ _)).symm ≪≫
    tensorIso (U.mapDerivedCategoryFactors.app P.complex).symm
      (U.mapDerivedCategoryFactors.app Q.complex).symm ≪≫
    tensorIso (U.mapDerivedCategory.mapIso P.iso) (U.mapDerivedCategory.mapIso Q.iso)

/-- Closed transposition of the actual tensor comparison and evaluation.
Source: Stacks 08J9 (blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def fixedHomComparison (X : Scheme.{u}) (n : ℕ)
    (M N : D (Scheme.ProEt.topology X) (coefficients l E X n)) :
    (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory.obj
      ((internalHom.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients l E X n)).obj (op M, N)) ⟶
    ((derivedHom (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) X).obj
      (op ((finiteUnrealization X
        (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory.obj M))).obj
      ((finiteUnrealization X
        (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory.obj N) := by
  letI := DerivedCategory.symmetricCategory
    (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)))
  let U := (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory
  let S := (calculus l E X).levelClosed n
  let H := (internalHom.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients l E X n)).obj (op M, N)
  exact (derivedTensorHomAdjunction
    (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) (U.obj M)).homEquiv _ _
    ((β_ (U.obj M) (U.obj H)).hom ≫ (fixedTensorComparison l E X n H M).inv ≫
      U.map (S.evaluation M N))

/-- Reduction of any integral complex is cartesian for derived coefficient extension.
Source: Zheng 4.1 (blueprint: def-sfb-coherent-hom-evaluation-transport).
Proof: evaluate reductionScalar.evaluation at both vertices. The constant system
has identity transitions; transitivity of derived scalar extension identifies
each reduction with the same extension from the integral coefficient ring. The
normalized scalar-unit and transpose formulas identify the horizontal map. -/
theorem reduction_normalized (X : Scheme.{u})
    (M : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (internalRing X (Padic.coefficientExtensionIntegers l E)))) :
    Normalized (Scheme.ProEt.topology X) (coefficients l E X)
      (transitions l E X) (calculus l E X).scalar ((reduction l E X).obj M) := by
  sorry

/-- The global finite-site comparison: apply the derived comparison unit and Leray,
then apply the closed-Hom comparison. It is defined before asserting it invertible.
Source: Stacks 099V, 08J9
(blueprint: def-sfb-coherent-hom-evaluation-transport). -/
def finiteSiteHomMap (X : Scheme.{u}) (n : ℕ)
    (M N : Etale.DerivedCategoryModule (Etale.FiniteProperQuotient.Ring l E n) X) :
    (Etale.FiniteProperQuotient.finiteHomScalars l E X n M).obj N ⟶
      ((derivedHom (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) X).obj
        (op ((nu l E X n).obj M)) ⋙
        rightDerivedGlobalSections
          (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) X ⋙
        finiteScalarRestrictionD l E n).obj
          ((nu l E X n).obj N) := by
  let A := ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)
  let H := ((Etale.derivedHom A X).obj (op M)).obj N
  exact (finiteScalarRestrictionD l E n).map
    ((Etale.rightDerivedGlobalSections A X).map
      ((derivedComparisonAdjunction A X).unit.app H) ≫
    (comparisonLowerStarCompRightDerivedGlobalSectionsIso A X).hom.app
      ((nu l E X n).obj H) ≫
    (rightDerivedGlobalSections A X).map (siteComparisonEvaluationHom
      A X M N))

end AlgebraicGeometry.ProEtale.CoherentReduction
