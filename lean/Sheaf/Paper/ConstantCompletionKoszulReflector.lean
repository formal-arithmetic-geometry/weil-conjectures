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
public import Sheaf.Paper.ConstantCompletionCore

/-!
# Constant coefficient completion: KoszulReflector

The Koszul reflector identification `koszul_quotient_reflector`.

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

/-- Koszul and finite-quotient completion are canonically identified, preserving the units;
their common functor is the reflector for the local internal-Hom completeness condition.
Source: Stacks 099L, 099M, 0A0E
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply the ringed Koszul reflector to the global generators, including the empty
list. For constant coefficients the Noetherian Koszul augmentation has pro-zero cone.
Exact constant sheafification and tensor by a fixed K-flat model preserve this property.
The strict-tower derived-limit theorem inverts the augmentation and identifies its unit
with the quotient unit. For completed coefficients, restrict to constant coefficients:
the finite reductions, strict Koszul tensors and units agree, and restriction identifies
total derived limits by the flat exact adjunction on strict towers. Conservativity
of exact restriction detects the augmentation isomorphism over the completion as well.
Transport the reflector property and the unit-isomorphism criterion across this
unit-preserving natural isomorphism. -/
theorem koszul_quotient_reflector [IsNoetherianRing A] (b : Bool) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = I) :
    ∃ K : KoszulPresentation J A I b r a,
      (∃ e : koszulCompletion J A I K ≅ completion J A I b,
        ∀ M : D (coefficients J A I b), koszulUnit J A I K M ≫ e.hom.app M =
          (completionUnit J A I b).app M) ∧
      (∀ M : D (coefficients J A I b),
        IsComplete (finiteMap J A I b 0) ((completion J A I b).obj M)) ∧
      (∀ (M L : D (coefficients J A I b)), IsComplete (finiteMap J A I b 0) L →
        Function.Bijective (fun f : (completion J A I b).obj M ⟶ L ↦
          (completionUnit J A I b).app M ≫ f)) ∧
      (∀ M : D (coefficients J A I b),
        IsIso ((completionUnit J A I b).app M) ↔ IsComplete (finiteMap J A I b 0) M) := by
  sorry

end CategoryTheory.ConstantCompletion
