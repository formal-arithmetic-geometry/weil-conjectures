/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Sheaf.Paper.FlatRingedIdealCompleteEquivalence
public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Sheaf.Paper.ConstantCompletionFinitePull

/-!
# Constant coefficient completion: PullbackComposition

Composition coherence of the pullback comparison (`pullback_composition`).

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation
variable {J A I}
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
attribute [local semireducible] completed
attribute [local irreducible] completed
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] derivedPull pull change
variable {C'' : Type u} [SmallCategory C''] {J'' : GrothendieckTopology C''}
variable {L₂ : Sheaf J' (Type u) ⥤ Sheaf J'' (Type u)}
variable (G : InverseImageData L₂) (H : InverseImageData (L ⋙ L₂))
variable (V₂ : Sheaf J'' (Type u) ⥤ Sheaf J' (Type u)) (adj₂ : L₂ ⊣ V₂)
variable [PreservesFiniteLimits L₂]

/-- The unreduced comparison is coherent for composite topos inverse images.
The composition isomorphisms are normalized by actual tensor insertions and their
K-flat computations. Consequently this also gives composition coherence for the finite
comparison, which is uniquely determined by its inverse equation.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: ordinary tensor associativity sends the twice-inserted element to 1 tensor m.
The coefficient maps for the composite agree after every finite projection, hence agree
by the limit universal property. This gives the two normalized ordinary isomorphisms.
All pullbacks preserve the flat-term K-flat resolving class, so these isomorphisms
descend to the displayed derived composition isomorphisms. On that class both sides of
the final equation insert 1 twice. Associativity identifies them, and localization
extends the equality to all derived objects. Uniqueness gives the finite coherence. -/
theorem pullback_composition (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ (aR : pull H (constantMap H A) ≅
        pull F (constantMap F A) ⋙ pull G (constantMap G A))
      (aB : pull H (completedMap H A I) ≅
        pull F (completedMap F A I) ⋙ pull G (completedMap G A I))
      (αR : (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) (constantMap H A)).functor ≅
        (derivedPull F V adj (constantMap F A)).functor ⋙
          (derivedPull G V₂ adj₂ (constantMap G A)).functor)
      (αB : (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) (completedMap H A I)).functor ≅
        (derivedPull F V adj (completedMap F A I)).functor ⋙
          (derivedPull G V₂ adj₂ (completedMap G A I)).functor),
      IsPullComposition F G H (constantMap F A) (constantMap G A) (constantMap H A) aR ∧
      IsPullComposition F G H (completedMap F A I) (completedMap G A I)
        (completedMap H A I) aB ∧
      IsDerivedPullComposition F V adj G H V₂ adj₂
        (constantMap F A) (constantMap G A) (constantMap H A) aR αR ∧
      IsDerivedPullComposition F V adj G H V₂ adj₂
        (completedMap F A I) (completedMap G A I) (completedMap H A I) aB αB ∧
      (∀ M : D (completed J A I),
        (derivedPullComparison H (V₂ ⋙ V) (adj.comp adj₂) A I).app M ≫
            (dres (coefficientMap J'' A I)).map (αB.hom.app M) =
          αR.hom.app ((dres (coefficientMap J A I)).obj M) ≫
            (derivedPull G V₂ adj₂ (constantMap G A)).functor.map
              ((derivedPullComparison F V adj A I).app M) ≫
            (derivedPullComparison G V₂ adj₂ A I).app
              ((derivedPull F V adj (completedMap F A I)).functor.obj M)) := by
  sorry

end CategoryTheory.ConstantCompletion
