/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Helper.SequentialSemilinearDerivedDiagramsDefs
public import WeilConjectures.Algebra.Homology.SequenceCoinduced.SystemCoinducedAdjunction
public import WeilConjectures.CategoryTheory.CoinducedSequence.CoinducedSequenceFunctoriality
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.Algebra.Homology.System.SystemOrdinarySingleExtension
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-! # The actual coinduced products for semilinear systems

Source: Stacks 0941, 015F and 079P; the locally finite resolution in
`lem-sf-sequential-semilinear-derived-exact`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived.Coinduced

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

abbrev derivedRight (n : ℕ) := (SequenceCoinduced.rightExtension B n).mapDerivedCategory

abbrev derivedAdjunction (n : ℕ) :=
  (SequenceCoinduced.adjunction B n).mapExactDerivedCategory

abbrev product (N : DerivedCategory (StrictRingSystem B)) :=
  CoinducedSequence.product (derivedSystemEvaluation B) (derivedRight B) N

abbrev relations (N : DerivedCategory (StrictRingSystem B)) :=
  CoinducedSequence.relations (derivedSystemEvaluation B) (derivedRight B)
    (Helper.adjacentRestriction B) N

abbrev augmentation (N : DerivedCategory (StrictRingSystem B)) :=
  CoinducedSequence.augmentation (derivedSystemEvaluation B) (derivedRight B)
    (derivedAdjunction B) N

-- The sign here is chosen to agree with Helper.difference.
def difference (N : DerivedCategory (StrictRingSystem B)) : product B N ⟶ relations B N :=
  -CoinducedSequence.difference (derivedSystemEvaluation B) (derivedRight B)
    (derivedAdjunction B) (Helper.adjacentRestriction B)
    (fun n ↦ systemDerivedTransition B (Nat.le_succ n)) N

abbrev productFunctor :=
  CoinducedSequence.productFunctor (derivedSystemEvaluation B) (derivedRight B)

abbrev relationsFunctor :=
  CoinducedSequence.relationsFunctor (derivedSystemEvaluation B) (derivedRight B)
    (Helper.adjacentRestriction B)

abbrev productHomEquiv :=
  CoinducedSequence.productHomEquiv (derivedSystemEvaluation B) (derivedRight B)
    (derivedAdjunction B)

abbrev relationsHomEquiv :=
  CoinducedSequence.relationsHomEquiv (derivedSystemEvaluation B) (derivedRight B)
    (derivedAdjunction B) (Helper.adjacentRestriction B)

abbrev augmentationNat :=
  CoinducedSequence.augmentationNat (derivedSystemEvaluation B) (derivedRight B)
    (derivedAdjunction B)

abbrev differenceNat :=
  CoinducedSequence.differenceNat (derivedSystemEvaluation B) (derivedRight B)
    (derivedAdjunction B) (Helper.adjacentRestriction B)
    (fun n ↦ systemDerivedTransition B (Nat.le_succ n))

end SheafOfModules.SequentialDerived.Coinduced
