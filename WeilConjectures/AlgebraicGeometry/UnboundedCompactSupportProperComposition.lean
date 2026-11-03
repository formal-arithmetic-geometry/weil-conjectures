/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Unbounded compact supports composed with proper direct image

Source: Stacks Project, More on Étale Cohomology, Tags 0F7H, 0F7I, 0F7J and 0F7B (b)
(blueprint: lem-sf-unbounded-compact-support-proper-composition).

Blueprint use: the first paragraph of the proof of `lem-weil-delta-proper-pushforward`,
where composition of the ambient right adjoints identifies the dualizing objects, followed
by the sentence asserting `Rf_! = Rf_*` for proper `f`. The composition comparison and its
proper normalization below supply precisely these inputs.

The candidates, proper/open tower map and common-refinement comparisons are the existing
ordinary small-etale constructions. Two definitions assemble the proper normalization and
its composition comparison. The three statements specify arbitrary proper refinements,
their K-injective representatives and coherence, and normalization on every tower.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Compare a compact-support candidate for a proper morphism with its ordinary direct image,
using the trivial compactification and the canonical identity-open isomorphism.
Source: Stacks Project, Tag 0F7H
(blueprint: lem-sf-unbounded-compact-support-proper-composition). -/
noncomputable def unboundedEtaleProperCandidateIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      R((f)_*[ModuleCat.{u + 1} A]) :=
  rightDerivedLowerShriekOfCompactificationIso A c (Compactification.ofIsProper f) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
      Functor.leftUnitor _

/-- The proper-input composition comparison, assembled from the closure tower `c.ofComp d`,
the inverse proper normalization on its restricted compactification, the existing proper/open
tower map, and the common-refinement comparison to the requested output compactification.
Source: Stacks Project, Tag 0F7J
(blueprint: lem-sf-unbounded-compact-support-proper-composition). -/
noncomputable def unboundedEtaleProperCompositionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsProper f] [QuasiCompact g]
    (d : Compactification g) (c : Compactification (f ≫ g)) :
    R((f)_*[ModuleCat.{u + 1} A]) ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Functor.isoWhiskerRight (unboundedEtaleProperCandidateIso A f (c.ofComp d).restrict).symm
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A d (c.ofComp d) ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (d.comp (c.ofComp d)) c

section NormalizationModels
universe w₁ w₂ v₁ v₂ u₁ u₂
open CategoryTheory.Abelian CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  [HasKInjectiveResolutions C]
omit [HasKInjectiveResolutions C] in
universe w₃ v₃ u₃
variable {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]

omit [HasKInjectiveResolutions C] in
end NormalizationModels

end AlgebraicGeometry.Etale
