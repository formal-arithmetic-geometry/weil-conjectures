/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Associativity of canonical finite-coefficient derived pro-etale pullback comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D,
`lemma-derived-pullback-composition`, its K-flat representative computation and the
associativity of inverse-image comparisons
(blueprint: lem-trf-derived-pullback-coherence).
-/

@[expose] public section

set_option autoImplicit false
-- Replaying the sectionwise transport tactics for linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] proEtaleRingModuleAdjunctionNormalized
  proEtaleRingModuleUnitSection proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors
  CochainComplex.IsAcyclicTensorKFlat SheafOfModules.IsFlatOnSite
  proEtaleRingModulePullback proEtaleConstantRingComparison
  proEtaleCanonicalPullbackComposition
  proEtaleRingDirectImageMap

-- All data selected below are fixed by the existing normalization: the units fix the
-- adjunctions, the section formula fixes d, conjugation fixes a, and degree maps fix b.
-- The structure only exposes these determined witnesses from the existing theorem.

@[irreducible] private noncomputable def constantData
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    PullbackData h k (proEtaleConstantRing V A) (proEtaleConstantRing W A)
      (proEtaleConstantRing Z A) (proEtaleConstantRingComparison k A)
      (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison (h ≫ k) A)
      (proEtaleConstantRingCompositeCoefficients_eq h k A)
      (proEtaleConstantRingPullbackComposition h k A).symm := by
  apply Classical.choice
  have he : (proEtaleConstantRingPullbackComposition h k A).symm =
      eqToIso (congrArg
        (proEtaleRingDerivedPullback (h ≫ k) (proEtaleConstantRing V A)
          (proEtaleConstantRing Z A))
        (proEtaleConstantRingCompositeCoefficients_eq h k A).symm) ≪≫
          proEtaleCanonicalPullbackComposition h k (proEtaleConstantRing V A)
            (proEtaleConstantRing W A) (proEtaleConstantRing Z A)
            (proEtaleConstantRingComparison k A) (proEtaleConstantRingComparison h A) := by
    rw [proEtaleConstantRingPullbackComposition_eq]
    rfl
  rw [he]
  exact pullbackData_transport h k
    (proEtaleConstantRing V A) (proEtaleConstantRing W A) (proEtaleConstantRing Z A)
    (proEtaleConstantRingComparison k A) (proEtaleConstantRingComparison h A)
    (proEtaleConstantRingComparison (h ≫ k) A)
    (proEtaleConstantRingCompositeCoefficients_eq h k A)

@[irreducible] private noncomputable def ordinaryComp
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A (h ≫ k) ≅
      proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h :=
  (constantData h k A).a

@[irreducible] private noncomputable def directComp
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    proEtaleConstantRingPushforward A h ⋙ proEtaleConstantRingPushforward A k ≅
      proEtaleConstantRingPushforward A (h ≫ k) :=
  (constantData h k A).d

@[irreducible] private noncomputable def normalizedAdj
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f :=
  (constantData f (𝟙 Y) A).adjh

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry.Scheme
