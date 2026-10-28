/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData
import Sheaf.Paper.AdicReindexingIdentityFiniteCertificate
import Sheaf.Paper.AdicReindexingIdentityAssembly
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

/-- Identity part of normalized reindexing functoriality.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tags 07A4 and 099N.
This is one conjunct of the parent theorem. (blueprint: lem-sf-adic-reindexing-functoriality-id)
-/
theorem normalized_reindexing_identity
(C : FamilyCore l D)
    (h_moduleId_sections : ∀ (T : GeometricSpace D) (M : modules l T.base.left (C.data
      T).realization)
          (U : T.base.left.ProEtᵒᵖ)
          (x : ((modulePull l T.base.left (𝟙 _) (C.ring T T (Iso.refl _))).obj M).val.obj U),
        HEq (((C.moduleId T).hom.app M).val.app U x) x)
    (h_integral_normalization : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
          (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g))
    (h_sourceId_unit : ∀ (T : GeometricSpace D)
          (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
        letI := (C.data T).units
        HEq
          ((pullbackTensorCommonComposition l (PadicAlgCl l)
              (𝟙 T.base.left) (𝟙 T.base.left) M).hom ≫
            (C.sourceId T).hom.app
              ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
          (𝟙 ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))) :
    (∀ (T : GeometricSpace D)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
    letI := (C.data T).units
    (C.comparison T T (Iso.refl _)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleId T) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          ((ordinary l T.base.left (C.data T).realization).obj M) =
    (ordinary l T.base.left (C.data T).realization).map ((C.sourceId T).hom.app M)) := by
  obtain ⟨h_certificate⟩ := normalized_reindexing_identity_finite l D C
    h_moduleId_sections h_integral_normalization
  exact normalized_reindexing_identity_from_finite l D C h_certificate h_sourceId_unit

end WeilConjectures.AdicQbarRealization
