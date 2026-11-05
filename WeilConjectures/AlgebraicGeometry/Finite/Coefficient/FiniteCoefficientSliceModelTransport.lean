/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

/-! # Transport of supplied constant complexes on a slice

Source: Stacks Project, proetale.tex, Tags 099R, 099Y and 09AL
(blueprint: lem-weil-pbc-finite-coefficient-slice-model-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

namespace SliceModelTransportProof

section Scalars
universe a b
variable {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
  (Λ : Type (max a b)) [CommRing Λ]

variable (R : Sheaf J RingCat.{max a b})
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{max a b}] [J.WEqualsLocallyBijective AddCommGrpCat.{max a b}]

variable [HasSheafify J (ModuleCat.{max a b} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{max a b} Λ)]

end Scalars

section Coordinates

attribute [local irreducible] completedAdicChangeData pbcDerivedScalarAdjunction

variable (X : Scheme.{t}) (B : Type t) [CommRing B]
  (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
  (φ : adicConstantRing X B ⟶ R)

end Coordinates

end SliceModelTransportProof

end AlgebraicGeometry.Scheme
