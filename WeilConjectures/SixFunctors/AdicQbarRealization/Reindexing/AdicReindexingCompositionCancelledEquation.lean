/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
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

/-- Proposition for the cancelled composition equation at one finite integral stage.
Source: Bhatt--Scholze, Remark 6.8.15, composition paragraph; Hemo--Richarz--Scholbach,
Lemma 7.9. (blueprint: def-sf-adic-reindexing-functoriality-comp-cancelled-equation)
-/
def normalized_reindexing_composition_cancelled_equation
    (C : FamilyCore l D) (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left) : Prop :=
  letI := (C.data T).units
  letI := (C.data U).units
  letI := (C.data V).units
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := V.base.left) E
  let Q := sfRationalConstructibleLocalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left
  (C.comparison T V (g ≪≫ h)).hom.app (I.obj (Q.obj K)) ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleComp T U V g h) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((ordinary l V.base.left (C.data V).realization).obj (I.obj (Q.obj K))) ≫
      inv ((derivedPull l T.base.left g.hom (C.ring T U g)).map
        ((C.comparison U V h).hom.app (I.obj (Q.obj K)))) =
    (ordinary l T.base.left (C.data T).realization).map
        (pullbackTensorCommonComposition l (PadicAlgCl l) h.hom g.hom
          (I.obj (Q.obj K))).hom ≫
      (C.comparison T U g).hom.app
        ((commonStageDerivedPullback l (PadicAlgCl l) h.hom).obj (I.obj (Q.obj K)))

end WeilConjectures.AdicQbarRealization
