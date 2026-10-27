/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.NormalizedFiniteFibreModels

/-! # The normalized finite sf fibre in the realization presentation

Source: BS 6.8.14(2), 6.8.15; Stacks 099N(5); blueprint
`thm-zl-real-mixed-by-curves`, paragraph 7 and the local-operator convention
(blueprint: def-zl-normalized-finite-realization-fibre).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrontier
open AlgebraicallyClosedCoefficients (Coefficient)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
variable (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Scalar-extended point comparison through the normalized integral representative.
Source: BS 6.8.14(2), Stacks 099N(5)
(blueprint: def-zl-normalized-finite-realization-fibre). -/
def finiteCompletedPointIso (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme)
    (x : Spec (.of D.k) ⟶ X.scheme) :=
  let F := Coefficient.{u} l Ω E
  let ext := ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω E)
  let H := DerivedCategory.homologyFunctor
    (integralTowerModules.{u, u} l F (Spec (.of D.k))) 0
  let p := (pointCompletedSections D.k l F).mapIso
    (H.mapIso (finiteIntegralPointIso D l Ω X E K x))
  let t := (ModuleCat.extendScalars
    ((sfAdicCoefficientEmbedding.{u} l Ω E).comp
      (algebraMap (Padic.coefficientExtensionIntegers l F) F))).mapIso p
  ext.mapIso (finiteSfPointIso D l Ω X E K x) ≪≫
    (finiteTensorComp l Ω E).symm.app _ ≪≫ t

/-- The completed point section object in the sf small-field presentation.
Source: BS 6.8.14(2) (blueprint: def-zl-normalized-finite-realization-fibre). -/
def finiteCompletedPointFibre (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme)
    (x : Spec (.of D.k) ⟶ X.scheme) : ModuleCat.{u + 1} Ω :=
  let F := Coefficient.{u} l Ω E
  (ModuleCat.extendScalars ((sfAdicCoefficientEmbedding.{u} l Ω E).comp
    (algebraMap (Padic.coefficientExtensionIntegers l F) F))).obj
      ((pointCompletedSections D.k l F).obj
        ((DerivedCategory.homologyFunctor
          (integralTowerModules.{u, u} l F (Spec (.of D.k))) 0).obj
            ((purCoefficientModel l F (Spec (.of D.k))).functor.obj
              ((pbcActualCompletedPull x (pbcStageDatum.{u} l Ω E)).obj
                (finiteIntegralModel D l Ω X E K).obj))))

/-- The two named small-field presentations give the identical section object.
Source: BS 6.8.14(2), coefficient convention
(blueprint: def-zl-normalized-finite-realization-fibre).
Proof: unfold the two small fields to Shrink E and their transported field and algebra
instances. Their finite-dimensionality proofs are propositionally equal. Both scalar
maps are the valuation-ring inclusion followed by Shrink.algEquiv and the actual
subfield inclusion. Thus both sides evaluate the same completed pullback, apply the
same coefficient restriction, H0 and final-object sections, and form the same tensor.
-/
theorem finiteCompletedPointFibre_eq (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme)
    (x : Spec (.of D.k) ⟶ X.scheme) :
    finiteCompletedPointFibre D l Ω X E K x =
      (adicCalculusIntegralFiber l Ω X.scheme E D.k x).obj
        (finiteIntegralModel D l Ω X E K) := by
  sorry

/-- The fixed model's fibre comparison, oriented from integral sections to the
normalized common-stage fibre.
Source: BS 6.8.14(2) (blueprint: def-zl-normalized-finite-realization-fibre). -/
def finiteModelFibreIso (R : Realization D l Ω) (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme)
    (x : Spec (.of D.k) ⟶ X.scheme) :=
  let J := finiteIntegralModel D l Ω X E K
  (((R.models X).fiber_integral D.k x E).app J).symm ≪≫
    ((R.models X).fiber D.k x).mapIso
      ((R.models X).comparison.unitIso.app
        ((adicCalculusIntegralInclusion l Ω X.scheme E).obj J) ≪≫
          (R.models X).comparison.inverse.mapIso (finiteStageIso D l Ω R X E K))

/-- The canonical sf-to-realization fibre bridge. The data are the point counit,
exact H0/sections and tensor comparisons, normalized completed pullback, the fixed
integral fibre comparison, and the coefficient equivalence unit. No Weil or
classical local operator occurs in this construction.
Source: BS 6.8.14(2), 6.8.15; Stacks 099N(5)
(blueprint: def-zl-normalized-finite-realization-fibre). -/
def finiteRealizationFibreIso (R : Realization D l Ω) (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X.scheme)
    (x : Spec (.of D.k) ⟶ X.scheme) :=
  finiteCompletedPointIso D l Ω X E K x ≪≫
    eqToIso (finiteCompletedPointFibre_eq D l Ω X E K x) ≪≫
      finiteModelFibreIso D l Ω R X E K x

end WeilConjectures.ZlFrontier
