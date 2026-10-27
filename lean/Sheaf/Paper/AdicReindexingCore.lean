/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Normalized integral and common-stage reindexing

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- Exact reindexing and balanced scalar extension descend to the raw common-stage category.
Source: Bhatt--Scholze, Remark 6.8.15; HRS Lemma 7.9, integral comparison and descent
(blueprint: lem-sf-adic-reindexing-core).

Proof: Use sectionwise inverse image along each underlying scheme isomorphism. Its
coefficient map fixes the finite-extension-valued functions, and coefficient naturality
identifies the integral quotient projections and finite scalar transitions. Balanced scalar
extension gives the section-normalized IntegralReindex. Localize its cochain comparison
through the exact-derived factorizations and scalar-extension counits. Compose its inverse
with the specified completion-unit inverse and the integral realization isomorphisms; this
is precisely integralRealizationAgreement, including both mapping-fiber coordinates.
The scalar-compatibility equation for the specified completion unit makes these components
compatible with finite scalar extension. Naturality first descends through the raw finite
rationalizations and then through common-stage Hom groups: represent an arrow at a common
field, use naturality there, and cancel the two scalar comparisons. Equality at a larger
stage proves independence of representatives. The inverse components descend by the same
square. Construct tensor reindexing on total K-flat models by the homogeneous pure-tensor
map and descend it by the representative equation. Reindexing preserves K-flatness since
it is an exact monoidal equivalence. The coefficient unit pulls back to itself, supplying
the canonical common-stage unit assertion. For the ordinary identity and compositor use
sectionwise identity maps. For the source identity use the integral pullback identity and
descend it through rationalization and common-stage inclusion; its unit equation is the
identity of the specified pullback composition on the same representatives. These maps
retain the given objectwise data exactly. No linearity over the base field is used. -/
theorem exists_normalized_reindexing_core
    (d : ∀ T : GeometricSpace D, SpaceData l D T) :
    ∃ C : FamilyCore l D, C.data = d ∧
    (∀ (T : GeometricSpace D) (M : modules l T.base.left (C.data T).realization)
      (U : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (𝟙 _) (C.ring T T (Iso.refl _))).obj M).val.obj U),
    HEq (((C.moduleId T).hom.app M).val.app U x) x)
    ∧ (∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
      (M : modules l V.base.left (C.data V).realization) (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (C.ring T V (g ≪≫ h))).obj M).val.obj W),
    HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    ∧ (∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
    letI := (C.data T).units
    letI := (C.data U).units
    integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
      (C.ring T U g) E (C.integral T U g E) (C.comparison T U g))
    ∧ (∀ (T : GeometricSpace D)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
    letI := (C.data T).units
    HEq
      ((pullbackTensorCommonComposition l (PadicAlgCl l)
          (𝟙 T.base.left) (𝟙 T.base.left) M).hom ≫
        (C.sourceId T).hom.app
          ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
      (𝟙 ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))) := by
  sorry

end WeilConjectures.AdicQbarRealization
