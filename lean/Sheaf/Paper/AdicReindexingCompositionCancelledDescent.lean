/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.AdicReindexingCompositionCancelledStage
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

/-- Common-stage descent for the cancelled composition equation.

Source: Bhatt--Scholze, Remark 6.8.15, composition paragraph; Hemo--Richarz--Scholbach,
Lemma 7.9. The finite-stage equation is transported through the specified localization,
common-stage inclusion and representative isomorphisms. Naturality and cancellation of the
intermediate scalar comparisons make the result independent of the chosen finite stage.
(blueprint: lem-sf-adic-reindexing-functoriality-comp-cancelled-descent)
-/
theorem normalized_reindexing_composition_cancelled_descent
(C : FamilyCore l D)
    (h_moduleComp_sections : ∀ (T U V : GeometricSpace D)
          (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
          (M : modules l V.base.left (C.data V).realization) (W : T.base.left.ProEtᵒᵖ)
          (x : ((modulePull l T.base.left (g ≪≫ h).hom
            (C.ring T V (g ≪≫ h))).obj M).val.obj W),
        HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (h_stage : ∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
      (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (K : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left),
      normalized_reindexing_composition_cancelled_equation l D C T U V g h E K) :
    ∀ (T U V : GeometricSpace D)
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
  sorry

end WeilConjectures.AdicQbarRealization
