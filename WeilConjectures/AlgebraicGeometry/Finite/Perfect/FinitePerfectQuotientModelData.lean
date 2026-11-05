/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicIntrinsicCompletion
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Data for finite perfect quotient models

Source: Stacks Tags 09C2 and 094I
(blueprint: def-weil-pbc-finite-perfect-quotient-model-data).

This interface records finite-level models without asserting a completed realization.
All coefficient identifications are normalized on constant sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

/-- The locally bijective characterization at the actual coefficient universe.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: the small pro-etale site is essentially small in universe t+1. -/
theorem finitePerfectModelsAbLocallyBijective (X : Scheme.{t}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Standard algebraic derived localization.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsAlgebraHasDerived (A : Type t) [CommRing A] :
    HasDerivedCategory (ModuleCat.{t} A) := HasDerivedCategory.standard _
/-- Standard derived localization for the actual coefficient sheaves.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsRingHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    HasDerivedCategory (SheafOfModules.{t + 1} R) := HasDerivedCategory.standard _
/-- Local bijectivity on the concrete localized site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceAbLocallyBijective (X : Scheme.{t}) (U : X.ProEt) :
    ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
/-- Standard derived localization on each slice.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt) :
    HasDerivedCategory (SheafOfModules.{t + 1} (R.over U)) :=
  HasDerivedCategory.standard _

end AlgebraicGeometry.Scheme
