/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.ScalarRoosComparison

/-! # Normalized scalar change and the whole-system Roos counit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit

/-- The normalized scalar realization commutes with the whole-system counit in
Roos coordinates. This is an equation on the target system alone, before inserting
any map from a good complex or identifying any strict zero-shift lift.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-counit-normalization)

Proof in words: resolve the restricted target diagram simultaneously by a
K-injective diagram. The normalized Roos bridge identifies its derived-limit
counit with the ordinary compatible limit tuple followed by the resolution
inverse. Present a flat-term K-flat source by its coherent quotient system and
apply the scalar realization normalization to that presentation. Transpose its
quotient tensor unit through the ordinary scalar adjunction. The residue square
identifies this transpose with the coordinates of a. The universal cochain
counit and the coefficient-action counit identify the resulting composite with
scalarRoosMap followed by the Roos map of a; both cocone coordinates are used.
Naturality and uniqueness of the derived comparison descend the equation from
these good representatives to the arbitrary derived limit of D. The specified
tensor coordinates determine a by the tensor and sheafification universal
properties. No zero-shift hypothesis on a map into the Roos complex is used.
-/
theorem scalarModelRoos_counit_normalization
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (a :
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        D).asFunctor ⋙ completedOrdinaryScalarComplex l L F j X ⟶
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor)
    (ha : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (x : (D.X i).val.obj (op (n, U.unop))),
      ((a.app (op n)).f i).val.app U
        (completedScalarTensorSection l L F j X
          (((coefficientSequenceRestriction l L X).obj (D.X i)).obj (op n)) U s
          (integralComparisonRestrictedSection l L X (D.X i) n U x)) =
        integralComparisonRestrictedSection l F X
          ((integralComparisonSequenceScalarModel l L F j X).E.obj (D.X i)) n U
          (integralComparisonSequenceTensorSection l L F j X (D.X i)
            (op (n, U.unop))
            ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) x)) :
    (completedDerivedScalarExtension l L F j X).map
        (integralComparisonRoosBridge l L X ρL D).inv ≫
      (completedScalarComparison l L F j X).app
        ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
      b.realization.hom.app
        ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l L F j X).map
          (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
      (integralComparisonRoosBridge l F X ρF _).hom =
    completedScalarCounit l L F j X
      (integralOperationsRoos
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
          D).asFunctor) ≫
      DerivedCategory.Q.map
        (scalarRoosMap (completedOrdinaryScalarExtension l L F j X)
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            D).asFunctor ≫ integralOperationsRoosMap a) := by sorry

end WeilConjectures
