/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingTensorCompatibility
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingUnitContraction

/-! # Unit compatibility of a normalized realization comparison

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9. The normalization calculation below is an
agent-written refinement of these comparison results.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- The unit equation for one fixed scheme-isomorphism comparison.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-reindexing-unit-compatibility).

Proof: Represent the common-stage coefficient unit by the degree-zero coefficient
complex at a finite coefficient field. Its ordinary realization is fixed by At.unit
and At.left_unit: tensoring the unit arrow with an identity, then applying the tensorator
and the source left unitor, is the ambient left unitor. The finite tensor normalization
therefore fixes this unit arrow, rather than allowing an arbitrary scalar multiple.
Substitute integralRealizationAgreement at this representative. The integral balanced
pullback and unit_sections identify the ordinary reindexing unit on each coefficient
section with the coefficient-ring map, which sends one to one. The quotient completion
coaugmentation has its quotient coordinate and zero shifted coordinate, so the same
equality holds before passing to the derived category. The unitor equation in the
specified canonicalCommonStagePullbackTensor_unit witness fixes its chosen source-unit
isomorphism: cancel the invertible tensor comparison and the left unitor. Apply the
ordinary realization and cancel the integral comparison and completion isomorphisms.
Raw rationalization and the common-stage unit identifications give the displayed
unit equation for that specified witness. No identity, composition or internal-Hom
compatibility of the realization comparison is assumed. -/
theorem normalized_reindexing_unit_compatibility
    (C : FamilyCore l D) (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (h_integral_normalization : ∀ (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g)) :
    letI := (C.data T).units
    letI := (C.data U).units
    (derivedPull l T.base.left g.hom (C.ring T U g)).map (C.data U).tensor.unit.hom ≫
      (C.comparison T U g).inv.app (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left) ≫
      (ordinary l T.base.left (C.data T).realization).map
        (C.unit_spec T U g).exists.choose.hom =
      (pullUnit l T.base.left g.hom (C.pullTensor T U g)).hom ≫ (C.data T).tensor.unit.hom := by
  let := (C.data T).units
  let := (C.data U).units
  have h := normalized_reindexing_tensor_compatibility l D C T U g
    h_integral_normalization
    (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)
    (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)
  exact reindexing_tensor_unit_contraction l D C T U g
    h

end WeilConjectures.AdicQbarRealization
