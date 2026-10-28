/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData
import Sheaf.Paper.QuotientSectionPullTransportKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.QuotientSectionPullTransportLocalizationIso
import Sheaf.Paper.IntegralResidueDerivedMonoidal
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-! # Localization descent for normalized quotient section pull transport -/

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

/-- Equality of the normalized computation maps on flat-term K-flat representatives
descends through the derived localization to every complex, once the ordinary witness
`e` is fixed.

Source: Stacks 06YS and 06YU; resolving-class/localization descent in the proof of
the quotient section pull transport theorem.
(blueprint: lem-sfb-quotient-section-pull-transport-extension-localization)
-/
theorem section_pull_normalized_localization_descent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T)
    (e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E)
    (hflat : ∀ P : CochainComplex (modules Λ Y) ℤ,
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
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)) :
    ∀ P : CochainComplex (modules Λ Y) ℤ,
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P) := by
  classical
  intro P
  let := SheafOfModules.monoidalCategory (ring Λ Y)
  let := SheafOfModules.symmetricCategory (ring Λ Y)
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients
    (R := ring Λ Y)).some
  let := SheafOfModules.hasFunctorialFlatResolution_kfi (ring Λ Y)
  let : IsGrothendieckAbelian.{u + 1} (modules Λ Y) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (Scheme.ProEt.topology Y) _
  obtain ⟨P', q, hq, hflat', hP'⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
  let e' : DerivedCategory.Q.obj P' ≅ DerivedCategory.Q.obj P :=
    asIso (DerivedCategory.Q.map q)
  exact section_pull_normalized_localization_transport_iso a f cX cY barLam e P' P e'
    (hflat P' hP' hflat')

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
