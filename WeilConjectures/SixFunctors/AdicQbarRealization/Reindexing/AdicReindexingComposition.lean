/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingCompositionCancelled
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- Composition part of normalized reindexing functoriality.
Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
This is one conjunct of the parent theorem. (blueprint: lem-sf-adic-reindexing-functoriality-comp)
-/
theorem normalized_reindexing_composition
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
          ((ordinary l V.base.left (C.data V).realization).obj M) =
    (ordinary l T.base.left (C.data T).realization).map
        (pullbackTensorCommonComposition l (PadicAlgCl l) h.hom g.hom M).hom ≫
      (C.comparison T U g).hom.app
        ((commonStageDerivedPullback l (PadicAlgCl l) h.hom).obj M) ≫
      (derivedPull l T.base.left g.hom (C.ring T U g)).map ((C.comparison U V h).hom.app M) := by
  intro T U V g h M
  letI := (C.data T).units
  letI := (C.data U).units
  letI := (C.data V).units
  let d := (derivedPull l T.base.left g.hom (C.ring T U g)).map
    ((C.comparison U V h).hom.app M)
  have hd := normalized_reindexing_composition_cancelled l D C
    h_moduleComp_sections h_integral_normalization T U V g h M
  let A := (C.comparison T V (g ≪≫ h)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleComp T U V g h) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((ordinary l V.base.left (C.data V).realization).obj M)
  let R := (ordinary l T.base.left (C.data T).realization).map
        (pullbackTensorCommonComposition l (PadicAlgCl l) h.hom g.hom M).hom ≫
      (C.comparison T U g).hom.app
        ((commonStageDerivedPullback l (PadicAlgCl l) h.hom).obj M)
  have hd' : A ≫ inv d = R := by
    simpa only [A, R, d, Category.assoc] using hd
  calc
    _ = A := by rfl
    _ = (A ≫ inv d) ≫ d := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    _ = R ≫ d := by rw [hd']
    _ = _ := by simp only [R, d, Category.assoc]

end WeilConjectures.AdicQbarRealization
