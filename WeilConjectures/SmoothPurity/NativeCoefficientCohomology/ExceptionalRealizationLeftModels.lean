/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CoefficientRealization.CoefficientRealizationData
public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientEndpointObjects
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData

/-! # Normalized realization of the exceptional left functor

The data here concern ordinary realization and compact support. They quantify over
no exceptional native right adjoint. In particular, no right-action comparison is
included in these data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
attribute [local instance 1100] CategoryTheory.instOverClass
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius
namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]
  (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

attribute [local instance] nativeStructureOver pointFiniteType pointQuasiCompact
  pointSeparated pointMapSeparated pointMapFiniteType pointMapQuasiCompact
  sourceFiniteType sourceQuasiCompact targetFiniteType targetQuasiCompact
  geometricMapOver geometricMapSeparated geometricMapFiniteType geometricMapQuasiCompact
  sourceUnits targetUnits

local instance coefficientDifferent : Fact (P.coefficients.l ≠ P.field.p) :=
  ⟨P.coefficients.different⟩

/-- The same source model in the native exceptional-forgetting interface.
Source: cor-coef-verdier-weil-equivariance.proof.md.
(blueprint: lem-sf-exceptional-realization-left-models) -/
def exceptionalReferenceSpace : NativeExceptionalForgetful.Space P.field where
  base := X₀
  separated := inferInstance
  finiteType := inferInstance
  quasiCompact := inferInstance

/-- An ordinary realization and models of native forgetting, together with the
normalized compact-support comparison. The Frobenius equation is a left square.
The reference fields identify this square with the published coefficient
presentation; they assert no right comparison.
Source: cor-coef-verdier-weil-equivariance.proof.md, scalar comparison and
exceptional-adjunction paragraph.
(blueprint: lem-sf-exceptional-realization-left-models) -/
structure ExceptionalRealizationLeftData where
  source : CoefficientRealization.Data P X₀
  sourceModel : WeilComplex P.field.k₀ P.coefficients.l X₀.left ⥤
    CoefficientRealization.Pairs P X₀
  targetModel : WeilComplex P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)) ⥤
    CoefficientRealization.Pairs P (point P.field)
  sourceRealization : sourceModel ⋙ CoefficientRealization.pairs P X₀ source ≅
    NativePairCohomology.native P.field.k₀ P.coefficients.l X₀.left
  pointUnit : targetModel.obj (WeilSheaf.toComplex.obj
      (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)))) ≅
    constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
      P.coefficients.different (point P.field) P.coefficients.Qbar
  left : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⋙
      targetModel ⋙ Endofunctor.IsoAlgebra.forget _ ≅
    (sourceModel ⋙ Endofunctor.IsoAlgebra.forget _) ⋙
      (operation P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀ (point P.field) (pointMap P.field X₀) c₀ S .closed).F
  left_frobenius : ∀ K : WeilComplex P.field.k₀ P.coefficients.l X₀.left,
    let O := operation P.field P.coefficients.l P.coefficients.different
      P.coefficients.Qbar X₀ (point P.field) (pointMap P.field X₀) c₀ S .closed
    let T := targetFrobenius P.field P.coefficients.l P.coefficients.different
      P.coefficients.Qbar (point P.field)
    O.F.map (sourceModel.obj K).str.hom ≫ left.inv.app K =
      (beta P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar
        X₀ (point P.field) (pointMap P.field X₀) c₀ S).inv.app
          (sourceModel.obj K).carrier ≫
        T.map (left.inv.app K) ≫
        (targetModel.obj
          ((WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom).obj K)).str.hom

  reference : AdicQbarRealization.Family P.coefficients.l P.field
  referencePackage : NativeExceptionalForgetful.Package P.field P.coefficients.l reference
  referenceSystem : NativeExceptionalForgetful.CoefficientSystem P.field P.coefficients.l
    (X := exceptionalReferenceSpace P X₀) (Y := NativeExceptionalForgetful.point P.field)
    (pointMap P.field X₀)
  sourceEquivalence : CoefficientRealization.Source P X₀ ≌
    NativeExceptionalForgetful.C P.field P.coefficients.l (exceptionalReferenceSpace P X₀)
  targetEquivalence : CoefficientRealization.Source P (point P.field) ≌
    NativeExceptionalForgetful.C P.field P.coefficients.l
      (NativeExceptionalForgetful.point P.field)
  functorComparison : sourceEquivalence.functor ⋙
      (referenceSystem.ring.operation
        (FrobeniusExchange.geometricCompactification P.field (pointMap P.field X₀) c₀)
          .closed).F ≅
    (operation P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar
        X₀ (point P.field) (pointMap P.field X₀) c₀ S .closed).F ⋙
      targetEquivalence.functor
  sourceModelComparison :
    (sourceModel ⋙ Endofunctor.IsoAlgebra.forget _) ⋙ sourceEquivalence.functor ≅
      (referencePackage.model (exceptionalReferenceSpace P X₀)).functor
  targetModelComparison :
    (targetModel ⋙ Endofunctor.IsoAlgebra.forget _) ⋙ targetEquivalence.functor ≅
      (referencePackage.model (NativeExceptionalForgetful.point P.field)).functor
  left_reference : ∀
      (J : WeilComplex P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)) ⥤
        WeilComplex P.field.k₀ P.coefficients.l X₀.left)
      (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J)
      (K : WeilComplex P.field.k₀ P.coefficients.l X₀.left),
    targetEquivalence.functor.map (left.inv.app K) ≫
        targetModelComparison.hom.app
          ((WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom).obj K) =
      functorComparison.inv.app (sourceModel.obj K).carrier ≫
        (referenceSystem.ring.operation
          (FrobeniusExchange.geometricCompactification P.field (pointMap P.field X₀) c₀)
            .closed).F.map (sourceModelComparison.hom.app K) ≫
        (referencePackage.comparison (exceptionalReferenceSpace P X₀)
          (NativeExceptionalForgetful.point P.field) (pointMap P.field X₀) referenceSystem
          (FrobeniusExchange.geometricCompactification P.field (pointMap P.field X₀) c₀)
          J adj).left.inv.app K

/-- Normalized ordinary realization models and the left compact-support square exist.
Source: cor-coef-verdier-weil-equivariance.proof.md, final paragraph; BS 6.8.14--15.
(blueprint: lem-sf-exceptional-realization-left-models)

Proof: take the normalized family of adic_qbar_constructible_realization. Restrict
IsAlgClosure.equiv from P.coefficients.Qbar to PadicAlgCl at every finite coefficient
field. The integral scalar functors and their balanced associators give a coherent
cocone, so common-stage descent gives the coefficient-change equivalence. Its
inverse is induced by the inverse field isomorphism. Compose with the family's
ordinary realization, the inverse section-module equivalence, and inverse-image
transport along the geometric-fibre isomorphism over k0. Finite representative
formulas give additivity, exactness, shifts, full faithfulness, and exactly the
bounded-constructible essential image. The family's normalized scheme-isomorphism
comparison at geometric Frobenius transports to Data.frobenius and its shift law.
Scalar-unit and pullback-unit normalization give Data.unit at both spaces.
Lift native ordinary forgetting through these fully faithful realizations, using
the bounded-constructible image. Lift its Frobenius structure and all its morphisms;
this gives sourceModel and targetModel and the retained source realization
isomorphism without
asserting fullness of derived forgetting. Full faithfulness lifts the normalized
point-unit isomorphism. Compose the native open/proper forgetting comparison with
the scalar-normalized comparison for the supplied geometric compactification and
system S. Lift this composite through the target realization to obtain left. Retain the
coefficient-change equivalences as sourceEquivalence and targetEquivalence. Their
finite scalar comparison gives functorComparison. Transporting the chosen native
forgetful models gives sourceModelComparison and targetModelComparison. Construct
referencePackage with the same left comparison for every supplied native adjunction,
as in the proof of native_exceptional_forgetful. Consequently left_reference is
exactly the equality defining the transported left comparison, uniformly in J.
These reference fields use only the left components of that package.
The scalar_frobenius_counit left-comparison equation, transported along precisely
the same coefficient and geometric-fibre equivalences, gives left_frobenius.
The equations are identities on integral representatives, hence survive passage to
raw rationalizations and common stages. Identity and empty schemes use these same
unit equations and the zero functor, respectively. No native right adjoint is used. -/
theorem exceptional_realization_left_models :
    Nonempty (ExceptionalRealizationLeftData P X₀ c₀ S) := by sorry

end WeilConjectures.NativeCoefficientCohomology
