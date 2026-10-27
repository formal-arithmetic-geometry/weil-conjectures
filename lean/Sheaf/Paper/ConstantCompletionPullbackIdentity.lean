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
# Constant coefficient completion: PullbackIdentity

Identity coherence of the pullback comparison (`pullback_identity`).

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

/-- The identity inverse image gives the identity scalar comparison under its normalized
ordinary and derived identity identifications. Source: Stacks 099L, 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the ordinary identity comparison multiplies 1 tensor m to m, fixing the stated
insertion equation. Descend termwise through the K-flat universal comparison to obtain
the derived identity isomorphisms. The scalar comparison inserts 1 and each identity
isomorphism removes it, so the final equality holds on the resolving class and hence
throughout the derived category. The inverse equation then gives the finite identity law. -/
theorem pullback_identity (F₀ : InverseImageData (𝟭 (Sheaf J (Type u))))
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ (aR : pull F₀ (constantMap F₀ A) ≅ 𝟭 (Mod (constant J A)))
      (aB : pull F₀ (completedMap F₀ A I) ≅ 𝟭 (Mod (completed J A I)))
      (αR : (derivedPull F₀ (𝟭 _) Adjunction.id (constantMap F₀ A)).functor ≅
        𝟭 (D (constant J A)))
      (αB : (derivedPull F₀ (𝟭 _) Adjunction.id (completedMap F₀ A I)).functor ≅
        𝟭 (D (completed J A I))),
      (∀ M : Mod (constant J A), pullInsertion F₀ (constantMap F₀ A) M ≫
        (underlying (constant J A)).map (aR.hom.app M) = 𝟙 _) ∧
      (∀ M : Mod (completed J A I), pullInsertion F₀ (completedMap F₀ A I) M ≫
        (underlying (completed J A I)).map (aB.hom.app M) = 𝟙 _) ∧
      (∀ P : Cx (constant J A), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        αR.hom.app ((Q (constant J A)).obj P) =
          (derivedPull F₀ (𝟭 _) Adjunction.id (constantMap F₀ A)).comparison.app P ≫
            (Q (constant J A)).map
              ((NatIso.mapHomologicalComplex aR (ComplexShape.up ℤ)).hom.app P)) ∧
      (∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        αB.hom.app ((Q (completed J A I)).obj P) =
          (derivedPull F₀ (𝟭 _) Adjunction.id (completedMap F₀ A I)).comparison.app P ≫
            (Q (completed J A I)).map
              ((NatIso.mapHomologicalComplex aB (ComplexShape.up ℤ)).hom.app P)) ∧
      (∀ M : D (completed J A I),
        (derivedPullComparison F₀ (𝟭 _) Adjunction.id A I).app M ≫
            (dres (coefficientMap J A I)).map (αB.hom.app M) =
          αR.hom.app ((dres (coefficientMap J A I)).obj M)) := by
  sorry

end CategoryTheory.ConstantCompletion
