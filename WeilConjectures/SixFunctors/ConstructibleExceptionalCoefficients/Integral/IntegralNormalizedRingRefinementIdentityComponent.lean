/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralNormalizedRingRefinementIdentityCore

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/--
The identity refinement component becomes the identity after the faithful integral
coefficient inclusion.  This is the pointwise identity calculation for the normalized
proper/open mate; faithfulness then lifts it to the comparison isomorphism.
Source: the identity diagram in the integral normalized refinement pasting argument
(blueprint: lem-sf-integral-normalized-ring-refinement-identity-component).
-/
theorem integral_normalized_ring_refinement_identity_component
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (N : CoefficientConstructionRefinements.{u, v} l Ω D hl R F M)
    (E : FieldStage.{max u v} l) (c : Compactification f)
    (K : C.{u, v} l Ω X (.integral E)) :
    (RingStage.inclusion.{u, v} l Ω Y (.integral E)).map
        ((N.refinement (.id c) (.integral E)).left.hom.app K) = 𝟙 _ := by
  obtain ⟨hi, hg, h⟩ := N.refinement_normalized (.id c) (.integral E)
  obtain ⟨ε, hε, hρ⟩ := h K
  dsimp at hi hg hε hρ ⊢
  have hcore :=
    integral_normalized_ring_refinement_identity_core.{u, v}
      ((RingStage.integral E).coefficients l) (c := c) hi hg
      ((RingStage.inclusion l Ω X (.integral E)).obj K) ε hε
  change (RingStage.inclusion l Ω Y (.integral E)).map
      ((N.refinement (.id c) (.integral E)).left.hom.app K) = 𝟙 _
  have hρ' :
      (R.left c (.integral E)).inv.app K ≫
          (RingStage.inclusion l Ω Y (.integral E)).map
            ((N.refinement (.id c) (.integral E)).left.hom.app K) ≫
        (R.left c (.integral E)).hom.app K =
      ((PurCompactSupport.geometricPushComposition
          ((RingStage.integral E).coefficients l)
          (Compactification.Refinement.id c).hom c.g hg ≪≫
        eqToIso (congrArg (fun h ↦ PurCompactSupport.push
            ((RingStage.integral E).coefficients l) h)
          (Compactification.Refinement.id c).hom_g)).symm.app
          ((PurCompactSupport.openExtension ((RingStage.integral E).coefficients l)
            c.i).mapDerivedCategory.obj
              ((RingStage.inclusion l Ω X (.integral E)).obj K))).hom ≫
        (PurCompactSupport.push ((RingStage.integral E).coefficients l) c.g).map ε.inv := by
    exact hρ
  have hcore' :
      ((PurCompactSupport.geometricPushComposition
          ((RingStage.integral E).coefficients l)
          (Compactification.Refinement.id c).hom c.g hg ≪≫
        eqToIso (congrArg (fun h ↦ PurCompactSupport.push
            ((RingStage.integral E).coefficients l) h)
          (Compactification.Refinement.id c).hom_g)).symm.app
          ((PurCompactSupport.openExtension ((RingStage.integral E).coefficients l)
            c.i).mapDerivedCategory.obj
              ((RingStage.inclusion l Ω X (.integral E)).obj K))).hom ≫
        (PurCompactSupport.push ((RingStage.integral E).coefficients l) c.g).map ε.inv =
      𝟙 ((PurCompactSupport.image ((RingStage.integral E).coefficients l) c).obj
        ((RingStage.inclusion l Ω X (.integral E)).obj K)) := by
    simpa [PurCompactSupport.image, Functor.comp_obj] using hcore
  apply (cancel_mono ((R.left c (.integral E)).hom.app K)).1
  simp only [Category.id_comp]
  apply (cancel_epi ((R.left c (.integral E)).inv.app K)).1
  simpa [PurCompactSupport.image, Functor.comp_obj, Category.assoc,
    Iso.inv_hom_id_app] using hρ'.trans hcore'

end WeilConjectures.ConstructibleExceptionalCoefficients
