/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.SixFunctors.FiniteDualizing
public import Sheaf.Paper.IntegralCompactSupportPrescribedReductions
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.SixFunctors.FiniteMappingAdjunction
public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import Sheaf.SixFunctors.CoefTowerNaturalCurrying
public import Sheaf.SixFunctors.NormalizedTowerTensorEvaluation

/-! # Finite adjunction construction data

Source: blueprint integral-dualizing proof, paragraph 2.
(blueprint: def-coef-finite-adjunction-transition-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace FiniteAdjunctionTransition

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The actual integral global mapping complex, with its R-module action.
Source: integral-dualizing proof, paragraph 2, first finite mapping complex
(blueprint: lem-coef-finite-adjunction-transition). -/
def H (r : ℕ) :=
  coefPairingIntegralHom l E X r (integralDualizingFiniteTerm l E D X r)

/-- Restrict the counit-defined tau to completed integral coefficients. The final
comparison is the section-normalized composition of actual restrictions.
Source: integral-dualizing proof, paragraph 2, left vertical map
(blueprint: lem-coef-finite-adjunction-transition). -/
def restrictedTau (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :=
  (scalarReductionDerivedRestriction l E X m).map
      (integralDualizingExceptionalTransition l E D X hl h) ≫
    (normalizedDVRResCompletedComp l E X D hl h).hom.app
      (integralDualizingFiniteTerm l E D X n)

/-- H_m to H_n is postcomposition by the actual restricted exceptional transition.
Source: integral-dualizing proof, paragraph 2, left vertical map
(blueprint: lem-coef-finite-adjunction-transition). -/
def HTransition (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (H D l E X m).obj (op K) ⟶ (H D l E X n).obj (op K) :=
  (coefPairingIntegralSections l E X).map
    ((coefficientIntegralInternalHom l E X).map
      (Prod.mkHom (𝟙 (op K)) (restrictedTau D l E X hl h)))

/-- C is exact coefficient-point sections of the integral compact-support Roos limit.
T and e below present the actual finite compact-support reduction tower, including
its transitions. This is the value to which prescribedReductions applies.
Source: integral-dualizing proof, paragraph 2, C=Gamma(s,Ra_!K)
(blueprint: lem-coef-finite-adjunction-transition). -/
abbrev C
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))))) :=
  coefCurryingIntegralSections l E D X T

/-- The coefficient-point dual J_r=RHom_R(C,A_r), contravariant in K.
Source: integral-dualizing proof, paragraph 2, right mapping complex
(blueprint: lem-coef-finite-adjunction-transition). -/
def J
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))))) (r : ℕ) :=
  (C D l E X T).op ⋙ coefCurryingPointHom l E r

/-- Postcomposition in RHom_R(C,-) by the genuine R-linear quotient A_m to A_n.
Source: integral-dualizing proof, paragraph 2, right vertical map
(blueprint: lem-coef-finite-adjunction-transition). -/
def JTransition
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
    {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (J D l E X T m).obj (op K) ⟶ (J D l E X T n).obj (op K) :=
  (ihom ((C D l E X T).obj K)).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
      (coefTraceQuotientMap l E h))

variable
  (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
  (a₀ b₀ : ℤ)
  (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
    DerivedCategory (pbcTowers (Spec (.of D.k))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
  (e : ∀ n : ℕ, T ⋙ pbcTowerEvaluation (Spec (.of D.k))
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n ≅
      compactSupportRestrictedLevel l E (finiteDualizingCompactification D X) n)
  (M : CoefCurryingModels l E D X Q a₀ b₀ T e)

/-- The point-section reduction comparison alpha_r is the scalar adjunct of the
actual Roos projection. Its adjunction has unit x mapped to 1 tensor x; the tower
transition equation fixes its successive-reduction normalization. In particular
this does not choose from point_sections_derived_reduction's Nonempty isomorphism.
Source: integral-dualizing proof, paragraph 2, prescribed reductions
(blueprint: lem-coef-finite-adjunction-transition). -/
def alpha (r : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
  CoefTower.reductionComparison D l E (finiteDualizingCompactification D X) T e r K

/-- Scalar adjunction on the full mapping complex, defined by base change of
normalized evaluation and the actual scalar adjunction counit. The finite tensor
comparison is normalized on K-flat representatives by M.calculus.
Source: integral-dualizing proof, paragraph 2, scalar-Hom identification
(blueprint: lem-coef-finite-adjunction-transition). -/
def scalarHom (r : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (H D l E X r).obj (op K) ⟶
      (coefPairingFiniteHom l E X r (integralDualizingFiniteTerm l E D X r)).obj (op K) :=
  (coefPairingIntegralSections l E X).map
    (coefficientEnrichedAdjunctionMap M.calculus.integralClosed (M.calculus.finiteClosed r)
      (coefficientFiniteDerivedExtension l E X r) (coefficientFiniteAdjunction l E X r)
      (M.calculus.finiteTensor r) K (integralDualizingFiniteTerm l E D X r))

/-- The specified horizontal map. The first factor is the evaluation-defined scalar
adjunction from integral Hom to finite Hom. The second factor is the finite mapping
adjunction pairing characterization: insert the
actual compact-support projection, balance scalars, apply projection and evaluation,
then the finite exceptional counit, and curry. In particular no independent alpha_r
is chosen from the point-reduction theorem's Nonempty statement.
Source: integral-dualizing proof, paragraph 2, gamma tilde
(blueprint: lem-coef-finite-adjunction-transition). -/
def finiteHorizontal (r : ℕ)
    (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory) :
    (H D l E X r).obj (op K.obj) ⟶ (J D l E X T r).obj (op K.obj) :=
  scalarHom D l E X Q a₀ b₀ T e M r K.obj ≫
    M.finiteArrow l E D X Q a₀ b₀ T e r K

end FiniteAdjunctionTransition
end WeilConjectures
