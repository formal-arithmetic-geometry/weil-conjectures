/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.PbcSupportCondition
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.SixFunctors.IntegralDualizing
public import Sheaf.SixFunctors.IntegralVerdier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Support and cosupport conditions at rational adic coefficients

Source: blueprint def-per-support-condition, both displayed conditions,
with the rational coefficient convention of lem-dl-a1-curve-intermediate-extension
(blueprint: def-per-support-condition).

The finite-coefficient definitions remain imported. Support here uses completed geometric
fibres of the actual integral representative, followed by inversion of the uniformizer.
Cosupport is support of RHom into the dualizing object. We quantify over its representing
objects rather than choose one: the displayed natural representing property determines
that object up to unique compatible isomorphism. In the finite-field application
prop-coef-integral-dualizing supplies it; in general this is the exceptional adjunction.
Thus this is precisely the usual cosupport predicate and does not choose extra data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Cohomology fibres use completed pullback, ordinary cohomology, exact point sections,
then inversion of the uniformizer, in that order. This also applies to an ambient dual.
Source: BS 6.8; blueprint support convention (blueprint: def-per-support-condition). -/
def qbarPerverseAmbientFiber (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X) (a : ℤ) :=
  (purCoefficientModel l E X).inverse ⋙
    pbcActualCompletedPull x (pbcIntegralDatum l E) ⋙
    DerivedCategory.homologyFunctor _ a ⋙ AlgebraicGeometry.Scheme.PerAdic.pointSections l E κ ⋙
    ModuleCat.extendScalars (AlgebraicGeometry.Scheme.PerAdic.integerToField l E)

/-- Closed cohomology support is the closure of the nonzero geometric-fibre locus.
Source: blueprint support convention (blueprint: def-per-support-condition). -/
def qbarPerverseAmbientSupport
    (K : DerivedCategory (scalarReductionSource l E X)) (a : ℤ) : Set X :=
  closure {x | ¬ IsZero ((qbarPerverseAmbientFiber l E X
    (AlgebraicClosure (X.residueField x)) (X.algClosurePoint x) a).obj K)}

/-- The support inequalities, including the empty-support convention in every degree.
Source: blueprint support convention (blueprint: def-per-support-condition). -/
def QbarPerverseAmbientSupportCondition
    (K : DerivedCategory (scalarReductionSource l E X)) : Prop :=
  ∀ i : ℤ, (qbarPerverseAmbientSupport l E X K (-i)).Nonempty →
    0 ≤ i ∧ topologicalKrullDim (qbarPerverseAmbientSupport l E X K (-i)) ≤ (i.toNat : ℕ∞)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The support condition in the literal common-stage category, evaluated on its
actual finite coefficient representative. Source: blueprint support convention
(blueprint: def-per-support-condition). -/
def QbarSupportCondition
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) : Prop :=
  QbarPerverseAmbientSupportCondition l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) X K.obj.obj.obj

variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]

/-- The canonical coherent reduction tower of compact support over an arbitrary field.
This is the same construction as integralDualizingCompactTower, without its redundant
finite-field specialization. Its terms, maps and quotient augmentations are prescribed
by exists_compactSupportReductionTower, not selected from a bare object existence.
Source: blueprint exceptional adjunction (blueprint: def-per-support-condition). -/
def qbarPerverseIntegralCompactTower :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of k))) := by
  letI := hasCompactification_of_finiteType_over_field k X (Spec (.of k))
    (X ↘ Spec (.of k))
  let h := exists_compactSupportReductionTower l E k X (Spec (.of k))
    (X ↘ Spec (.of k)) hl (HasCompactification.compactification (X ↘ Spec (.of k)))
  letI := h.choose
  letI := h.choose_spec.choose
  exact h.choose_spec.choose_spec.2.2.choose

/-- The actual compact-support value at the coefficient point, before sections.
Source: blueprint dualizing adjunction (blueprint: def-per-support-condition). -/
def qbarPerverseIntegralCompactSupport :=
  (sfIntegralConstructible l E X).ι ⋙ qbarPerverseIntegralCompactTower l E X k hl ⋙
    integralDualizingLimit l E (Spec (.of k))

/-- The coefficient unit in degree zero on the geometric point.
Source: blueprint dualizing adjunction (blueprint: def-per-support-condition). -/
def qbarPerverseIntegralPointUnit :
    DerivedCategory (scalarReductionSource l E (Spec (.of k))) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))))

/-- The natural representing property of the exceptional inverse image of the unit.
Yoneda makes its representing object unique up to compatible isomorphism.
Source: blueprint dualizing adjunction (blueprint: def-per-support-condition). -/
def QbarPerverseIntegralDualizingProperty (ω : sfIntegralConstructibleCategory l E X) : Prop :=
  Nonempty ((sfIntegralConstructible l E X).ι.op ⋙ yoneda.obj ω.obj ≅
    (qbarPerverseIntegralCompactSupport l E X k hl).op ⋙
      yoneda.obj (qbarPerverseIntegralPointUnit l E k))

/-- Cosupport is support of the dual. The integral dualizing representatives are exactly
those representing the exceptional adjunction against the coefficient unit.
Yoneda identifies any two, so universal quantification
expresses the canonical dual without arbitrary choices. RHom takes its actual integral
input, and fibre rationalization removes integral torsion before testing support.
Source: blueprint cosupport and class formulas (blueprint: def-per-support-condition). -/
def QbarCosupportCondition
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) : Prop :=
  ∀ ω : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) X,
    QbarPerverseIntegralDualizingProperty l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) X k hl ω →
    QbarPerverseAmbientSupportCondition l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) X
      ((IntegralVerdier.dual l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) X ω.obj).obj
          (op K.obj.obj.obj))

end WeilConjectures
