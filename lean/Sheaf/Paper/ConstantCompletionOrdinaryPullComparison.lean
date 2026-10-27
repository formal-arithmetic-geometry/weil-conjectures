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
public import Sheaf.Paper.ConstantCompletionInverseImage

/-!
# Constant coefficient completion: OrdinaryPullComparison

The ordinary scalar pullback comparison (`ordinaryPullComparison_existsUnique`).

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

/-- The unreduced scalar comparison on ordinary modules is fixed by scalar insertion.
This is exactly u^(-1)M → u^(-1)M tensor the completed coefficient ring after inverse image.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the finite projections make the coefficient square commute. After identifying
inverse images of constant coefficients, define q by m ↦ 1 tensor m. It is linear over
the constant coefficient sheaf, and natural in M. Pure tensors generate after
sheafification, so the insertion equation determines q uniquely. -/
theorem ordinaryPullComparison_existsUnique (A : Type u) [CommRing A] (I : Ideal A) :
    ∃! q : res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⟶
        pull F (completedMap F A I) ⋙ res (coefficientMap J' A I),
      ∀ M : Mod (completed J A I),
        pullInsertion F (constantMap F A) ((res (coefficientMap J A I)).obj M) ≫
            (underlying (constant J' A)).map (q.app M) =
          pullInsertion F (completedMap F A I) M := by
  sorry

end CategoryTheory.ConstantCompletion
