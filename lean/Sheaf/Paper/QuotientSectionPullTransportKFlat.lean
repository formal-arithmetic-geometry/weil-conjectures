/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData
import Sheaf.Paper.IntegralResidueDerivedMonoidal
import Sheaf.Paper.InternalScalarPullbackNormalizationData
import Sheaf.Paper.QuotientSectionPullTransportKFlatOrdinary
import Sheaf.Paper.QuotientSectionPullTransportKFlatDerived

/-! # Flat-term part of normalized quotient section pull transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

private def sectionPullTransportDerived {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) :
    cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T := by
  let e : (derivedEquivalence Λ Y).functor ⋙
        (cY.model.T ⋙ derivedPullback Λ' f) ≅
      (derivedEquivalence Λ Y).functor ⋙
        (derivedPullback Λ f ⋙ cX.model.T) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight cY.derived.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (scalarSectionPullComparison Λ' f).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight lam (derivedEquivalence Λ' X).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ cX.derived ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (scalarSectionPullComparison Λ f) _ ≪≫
      Functor.associator _ _ _
  exact ((Functor.whiskeringLeft _ _ _).obj
    (derivedEquivalence Λ Y).functor).preimageIso e

/-- The flat-term fragment of `SectionPullNormalized`. It retains the ordinary
section square and requires the derived computation square only on the flat-term
K-flat representatives used by localization descent.
Source: Stacks 06YS, 06YY, 0D6D and 0G7E; flat-term part of parent proof step 8.
(blueprint: lem-sfb-quotient-section-pull-transport-kflat).
-/
def SectionPullNormalizedOnKFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T) : Prop :=
  ∃ e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E,
    (∀ M : Modules Λ Y,
      (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
          cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          cX.model.E.map ((pullComparison Λ f).hom.app M) =
        (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
          (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
          e.hom.app ((equivalence Λ Y).functor.obj M)) ∧
    ∀ P : CochainComplex (modules Λ Y) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)

/-- Flat-term construction of the normalized section pullback comparison.
Proof: conjugate the ordinary pullback comparison through the endpoint scalar
models, then compute the derived map on flat-term K-flat representatives. The
ordinary generator equations in `ScalarSectionNormalized` identify the section
map, while `PullNormalized` identifies the derived computation square.
Localization descent is deliberately left to
`section_pull_transport_extend_kflat`.
(blueprint: lem-sfb-quotient-section-pull-transport-kflat). -/
theorem section_pull_transport_section_normalized_kflat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam) :
    ∃ barLam : cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T,
      SectionPullNormalizedOnKFlat a f cX cY barLam := by
  let barLam := sectionPullTransportDerived a f cX cY lam
  refine ⟨barLam, ?_⟩
  obtain ⟨e, he⟩ := section_pull_transport_kflat_ordinary a f cX cY hcX hcY
  refine ⟨e, he, ?_⟩
  exact section_pull_transport_kflat_derived a f cX cY hcX hcY lam hlam barLam e he

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
