/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData
import all Sheaf.Paper.CoefficientSectionsCoreTransport
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! The normalized scalar comparison for the prescribed coefficient sections.
Source: Stacks 079P and 0D6E. Restriction-of-scalars sections acyclicity makes the
composite a right derivation; its universal comparison gives the model equation.
(blueprint: lem-coef-sections-core-scalar-comparison)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.privateModule false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures



variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory HasDerivedCategory.standard

open SheafOfModules in
/-- The actual scalar section comparison with its normalization on every complex.
Source: Stacks 079P and 0D6E.
Proof: value at one identifies module-unit maps with compatible sections. Scalar
restriction preserves their underlying presheaf. Sections acyclicity makes the
unit invertible on restricted K-injective complexes, by resolving them and using
naturality. The exact-restriction composite and finite sections are right
derivations, so their universal comparison gives the isomorphism and unit equation.
(blueprint: lem-coef-sections-core-scalar-comparison) -/
private theorem scalarSectionsComparison (n : ℕ) :
    ∃ s : coefficientFiniteDerivedRestriction l E W n ⋙
        coefficientIntegralSections l E W ≅ coefficientFiniteSections l E W n,
      ∀ I : CochainComplex (scalarReductionTarget l E W n) ℤ,
        CoefficientComparisonEquation
          (coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)
            (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj I))
          ((coefficientIntegralSections l E W).map
            ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app I))
          (s.hom.app (DerivedCategory.Q.obj I))
          (DerivedCategory.Q.map (coefficientComplexCompositeSourceTransformation
            (scalarReductionRestriction l E W n)
            (coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W))
            (H := coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
              (integralCoefficientCommRingSheaf l E W n))
            (ordinaryRestrictionIso.{t+1, t, u} (Scheme.ProEt.topology W)
              (completedIntegralCommRingProjectionUnrestricted l E W n)).hom I))
          (coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n) I) := by
  let J := Scheme.ProEt.topology W
  let A := completedIntegralCommRingSheafUnrestricted l E W
  let B := integralCoefficientCommRingSheaf l E W n
  let F := coefficientOrdinarySections.{u, t+1, t} J A
  let G := coefficientOrdinarySections.{u, t+1, t} J B
  let : EssentiallySmall.{max u (t+1)} W.ProEt := essentiallySmallSelf _
  let : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionSource l E W) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      J A).1
  let : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionTarget l E W n) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      J B).1
  let : IsGrothendieckAbelian.{max u (t+1)} (SheafOfModules.{max u (t+1)}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      J A).1
  let : IsGrothendieckAbelian.{max u (t+1)} (SheafOfModules.{max u (t+1)}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      J B).1
  let P := siteSectionsPair.{t+1, t, u} J A
  let S := siteSectionsPair.{t+1, t, u} J B
  have hc (I : CochainComplex (scalarReductionTarget l E W n) ℤ) (hI : I.IsKInjective) :
      IsIso (P.unit.app
        (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj I)) := by
    have := hI
    let K := ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj I
    obtain ⟨L, hL, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    have := hj
    have hsec : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map j) :=
      ordinaryRestrictionSections_quasiIso.{t+1, t, u} J
        (completedIntegralCommRingProjectionUnrestricted l E W n) I L j
    have := P.computes L hL
    have hh := P.unit.naturality j
    dsimp only [Functor.comp_map] at hh
    have hi : IsIso (P.unit.app K ≫ P.functor.map (DerivedCategory.Q.map j)) := by
      rw [← hh]
      infer_instance
    exact IsIso.of_isIso_comp_right (P.unit.app K)
      (P.functor.map (DerivedCategory.Q.map j))
  have h := restrictionDerivedIso (scalarReductionRestriction l E W n) F G
    (ordinaryRestrictionIso.{t+1, t, u} J
      (completedIntegralCommRingProjectionUnrestricted l E W n)) P S hc
  exact h


end WeilConjectures
