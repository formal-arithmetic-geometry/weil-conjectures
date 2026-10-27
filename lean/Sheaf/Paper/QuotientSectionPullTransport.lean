/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData
import Sheaf.Paper.IntegralResidueDerivedMonoidal

/-! # A step of the normalized quotient section comparison -/

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

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

open ModuleRingedComparison

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The same normalized scalar models realize the specified scalar/pullback map.
Source: Stacks 03EL, 06YY, 0D6D and 0G7E; parent proof step 8.
(blueprint: lem-sfb-quotient-section-pull-transport).

Proof: conjugate the inverse of the ordinary internal pullIso by the two normalized
ordinary scalar comparisons and the fixed section pullback comparisons. This gives
the ordinary section balancing isomorphism, carrying inverse image of x tensor s
to inverse image of x tensor inverse image of s. The ordinary comparison equation
in SectionPullNormalized holds by construction. The geometric coefficient square
commutes by naturality of pullback from the point, so this formula respects scalars.
Both composites preserve flat-term K-flat resolutions. Derive the ordinary square
using the fixed pullback localization maps and the scalar model counits. This gives
barLam and its universal-counit computation square on all complexes. Conjugating
the given lam by the same comparisons has the same computation square, because
PullNormalized fixes lam by the actual internal counits. Uniqueness of the derived
comparison identifies these maps, giving PullSectionCondition. No coefficient
flatness, boundedness, nonemptiness or nonzero-module assumption is used. -/
theorem section_pull_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam) :
    ∃ barLam : cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T,
      PullSectionCondition a f cX cY lam barLam ∧
        SectionPullNormalized a f cX cY barLam := by sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
