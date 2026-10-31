/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingIdentity
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingComposition

/-! # Identity and composition of normalized reindexing

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

/-- The normalized integral realization comparisons respect actual pullback compositors.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks 07A4 and 03EL
(blueprint: lem-sf-adic-reindexing-functoriality).

Proof: For the identity, substitute integralRealizationAgreement. The ordinary identity
is fixed on sections, the completion-unit map is the identity under the specified
pullback identity, and the scalar and realization isomorphisms cancel. The source identity
is fixed by its unit equation for the specified composition. For composition substitute
the same integral formula for each of the three comparisons. The entire-cone composition
law for the specified completion units identifies their inverse factors; the balanced
scalar cochain composition law and the sectionwise ordinary compositor identify the
remaining factors. These are identities of derived maps, not merely of reductions.
The finite scalar square then transports both equalities through raw rationalization.
Every common-stage object has a finite integral representative up to the canonical
stage and localization isomorphisms; naturality transports the equalities along these
isomorphisms. The intermediate scalar comparisons cancel, giving exactly the displayed
identity and composition equations. -/
theorem normalized_reindexing_functoriality
    (C : FamilyCore l D)
    (h_moduleId_sections : ∀ (T : GeometricSpace D) (M : modules l T.base.left (C.data
      T).realization)
          (U : T.base.left.ProEtᵒᵖ)
          (x : ((modulePull l T.base.left (𝟙 _) (C.ring T T (Iso.refl _))).obj M).val.obj U),
        HEq (((C.moduleId T).hom.app M).val.app U x) x)
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
    (ordinary l T.base.left (C.data T).realization).map ((C.sourceId T).hom.app M))
    ∧ (∀ (T U V : GeometricSpace D)
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
      (derivedPull l T.base.left g.hom (C.ring T U g)).map ((C.comparison U V h).hom.app M))  := by
  constructor
  · exact normalized_reindexing_identity l D C h_moduleId_sections
      h_integral_normalization h_sourceId_unit
  · exact normalized_reindexing_composition l D C h_moduleComp_sections h_integral_normalization

end WeilConjectures.AdicQbarRealization
