/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingCompositionCancelledStage
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingCompositionCancelledDescent

/-! # Cancelled composition calculation for normalized adic reindexing

This is the representative and scalar calculation in the composition proof.  The
remaining derived-pullback comparison is an isomorphism and is restored by cancellation
in `AdicReindexingComposition`.
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

/--
The composition calculation after cancelling the final derived-pullback comparison.

Source: Bhatt--Scholze, Remark 6.8.15, composition paragraph; Hemo--Richarz--Scholbach,
Lemma 7.9.  The proof substitutes the three integral comparison formulas, applies the
entire-cone composition and balanced scalar cochain coherence equations, and transports
the resulting representative equality through finite realization and localization.
The final comparison is omitted here because it is an isomorphism; the parent theorem
restores it by `cancel_mono`.
(blueprint: lem-sf-adic-reindexing-functoriality-comp-cancelled)
-/
theorem normalized_reindexing_composition_cancelled
(C : FamilyCore l D)
    (h_moduleComp_sections : ∀ (T U V : GeometricSpace D)
          (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
          (M : modules l V.base.left (C.data V).realization) (W : T.base.left.ProEtᵒᵖ)
          (x : ((modulePull l T.base.left (g ≪≫ h).hom
            (C.ring T V (g ≪≫ h))).obj M).val.obj W),
        HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (h_integral_normalization : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
          (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g))
: ∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) V.base.left),
    letI := (C.data T).units
    letI := (C.data U).units
    letI := (C.data V).units
    (C.comparison T V (g ≪≫ h)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleComp T U V g h) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((ordinary l V.base.left (C.data V).realization).obj M) ≫
      inv ((derivedPull l T.base.left g.hom (C.ring T U g)).map
        ((C.comparison U V h).hom.app M)) =
    (ordinary l T.base.left (C.data T).realization).map
        (pullbackTensorCommonComposition l (PadicAlgCl l) h.hom g.hom M).hom ≫
      (C.comparison T U g).hom.app
        ((commonStageDerivedPullback l (PadicAlgCl l) h.hom).obj M) := by
  intro T U V g h M
  apply normalized_reindexing_composition_cancelled_descent l D C
    h_moduleComp_sections
  intro T U V g h E K
  exact normalized_reindexing_composition_cancelled_stage l D C
    h_moduleComp_sections h_integral_normalization T U V g h E K

end WeilConjectures.AdicQbarRealization
