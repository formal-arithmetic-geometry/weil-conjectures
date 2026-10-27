/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Paper.OrdinaryImmersionChartModels
import all Sheaf.Algebra.Homology.SitePerfectModelRestriction

/-! Ordinary completed coefficient geometry, before passage to derived categories. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.SubterminalImageCalculus.smallSheafify
attribute [-instance] CategoryTheory.SubterminalImageCalculus.smallLocalCriterion

universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OrdinaryImmersionChart

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem restrictExact {S : Scheme.{t}} (U : S.ProEt) :
    PreservesFiniteLimits (restrict l E U) ∧
      PreservesFiniteColimits (restrict l E U) := by
  have : (MorphismProperty.Over.map ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology S) := ProEt.isContinuous_overMap U.prop
  have : (MorphismProperty.Over.map ⊤ U.prop).IsCocontinuous
      (ProEt.topology U.left) (ProEt.topology S) := ProEt.isCocontinuous_overMap U.prop
  exact ⟨SheafOfModules.pushforward_finiteLimits _,
    SheafOfModules.pushforward_finiteColimits _⟩

/-- The underived restriction square on represented scheme charts, with the actual
section map and the unit/counit mate. Source: Stacks Tag 04IF.
(blueprint: lem-tw-ordinary-completed-chart-comparison). -/
structure OrdinaryChart {T S : Scheme.{t}} (g : T ⟶ S) (U : S.ProEt) where
  direct : push l E g ⋙ restrict l E U ≅
    restrict l E ((proEtaleBaseChange g).obj U) ⋙ push l E (completedRingSliceArrow g U)
  sections : ∀ (N : Modules l E T) (H : U.left.ProEt)
    (m : ((push l E g ⋙ restrict l E U).obj N).val.obj (op H)),
    (direct.hom.app N).val.app (op H) m =
      N.val.map (completedRingSlicePointIso g U H).hom.op m
  ordinary : restrict l E U ⋙ pull l E (completedRingSliceArrow g U) ≅
    pull l E g ⋙ restrict l E ((proEtaleBaseChange g).obj U)
  mate : ∀ M : Modules l E S, ordinary.hom.app M =
    (pull l E (completedRingSliceArrow g U)).map
      ((restrict l E U).map ((adj l E g).unit.app M)) ≫
    (pull l E (completedRingSliceArrow g U)).map
      (direct.hom.app ((pull l E g).obj M)) ≫
    (adj l E (completedRingSliceArrow g U)).counit.app
      ((restrict l E ((proEtaleBaseChange g).obj U)).obj ((pull l E g).obj M))

/-- Localization of the ordinary completed-coefficient ringed morphism at a
represented pro-etale object.
Source: Stacks Tags 04IF, 04J0 and 03CE.
(blueprint: lem-tw-ordinary-completed-chart-comparison).

Proof. Restriction to the represented slice is exact. The dense slice equivalence
identifies it with restriction to the pro-etale site of its representing scheme.
Transport its coefficients by the constant-section and finite-projection normalized
chartRingIso. Completed coefficient coherence identifies the resulting structural
map with completedRingMap of the slice arrow. Its direct-image comparison on H
is the module restriction map along completedRingSlicePointIso: naturality gives
additivity and compatibility with the scalar action. This is an isomorphism since
the point map is an isomorphism. Localize the module pullback adjunction at U.
The localized inverse image is identified by its adjunction with the pullback of
the slice arrow. The canonical localized comparison is invertible by the
finite-product comparison of base change. Its adjoint transpose is the restricted
global unit followed by the direct-image comparison. Applying the inverse Hom
bijection gives exactly the unit, direct-map, counit equation stated in mate. -/
theorem ordinaryCompletedChartComparison {T S : Scheme.{t}} (g : T ⟶ S) (U : S.ProEt) :
    Nonempty (OrdinaryChart l E g U) := by
  sorry

end WeilConjectures.OrdinaryImmersionChart
