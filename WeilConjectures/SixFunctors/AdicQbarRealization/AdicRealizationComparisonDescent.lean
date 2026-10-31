/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicRealizationReindexScalar
import WeilConjectures.CategoryTheory.StageSystem.StageComparisonNaturality

/-! # Common-stage realization comparison descent

This is the comparison and representative-agreement part of the integral descent
argument for one scheme isomorphism. Source: Bhatt--Scholze, Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-realization-comparison-descent)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/--
Given the balanced integral reindexings, the common-stage realization comparison
exists and agrees with each integral representative. The proof composes the
specified realization isomorphisms with the inverse derived balanced comparison
and the completion-unit comparison. Naturality is checked after representing an
arrow over one finite field; scalar extension uses the specified finite-free
comparison and the scalar compatibility square. The inverse components descend by
the same argument. This theorem asserts no tensor or identity/composition law.
 (blueprint: lem-sf-adic-realization-comparison-descent)
-/
theorem exists_realization_comparison_descent (D : FiniteFieldDatum.{u})
    (d : ∀ T : GeometricSpace D, SpaceData l D T)
    (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (B : RingReindex l T.base.left g.hom (d T).realization (d U).realization)
    (I : ∀ E, IntegralReindex l T.base.left g.hom B E) :
    letI := (d T).units
    letI := (d U).units
    ∃ c : commonStageDerivedPullback l (PadicAlgCl l) g.hom ⋙
        ordinary l T.base.left (d T).realization ≅
      ordinary l U.base.left (d U).realization ⋙ derivedPull l T.base.left g.hom B,
    ∀ E, integralRealizationAgreement l g.hom (d T).realization (d U).realization
      B E (I E) c := by
  let := (d T).units
  let := (d U).units
  let R := (d T).realization
  let S := (d U).realization
  let F := commonStageDerivedPullback l (PadicAlgCl l) g.hom ⋙ ordinary l T.base.left R
  let H := ordinary l U.base.left S ⋙ derivedPull l T.base.left g.hom B
  let e := fun E ↦ realizationRationalReindex l g.hom R S B E (I E)
  have he (P : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) U.base.left)
      (L : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) (h : P.stage ≤ L) :
      F.map ((GeneralAlgebraicallyClosedCoefficients.stageSystem l
          (PadicAlgCl l) U.base.left).isoToStage P h).hom ≫
          (e L).hom.app (P.toStage h) =
        (e P.stage).hom.app P.obj ≫
          H.map ((GeneralAlgebraicallyClosedCoefficients.stageSystem l
            (PadicAlgCl l) U.base.left).isoToStage P h).hom := by
    obtain ⟨E, ⟨K⟩⟩ := P
    rw [show (e E).hom.app ⟨K⟩ =
      (realizationIntegralReindex l g.hom R S B E (I E)).hom.app K from
        (realizationRationalReindex_existsUnique l g.hom R S B E
          (I E)).exists.choose_spec K]
    exact realizationIntegralReindex_scalar l g.hom R S B I E L h K
  let c : F ≅ H := NatIso.ofComponents (fun P ↦ (e P.stage).app P.obj)
    (fun f ↦ StageSystem.stageComparison_naturality
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) U.base.left)
      F H e he f)
  refine ⟨c, ?_⟩
  intro E
  apply realizationAgreement_of_components l g.hom R S B E (I E) c
  intro K
  change HEq ((e E).hom.app _) _
  exact heq_of_eq ((realizationRationalReindex_existsUnique l g.hom R S B E
    (I E)).exists.choose_spec K)

end WeilConjectures.AdicQbarRealization
