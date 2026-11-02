/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedTowerDirectImage
import all WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Completed pullback on the published completed-coefficient categories

Source: Stacks proetale.tex, Tag 099N (2),(5), blueprint order 1261.
(auxiliary; not a blueprint node)
The coefficient structure is fixed on all quotient projections. Ordinary pullback
is its total derived sheafified tensor inverse image. Completion is characterized
by its reflection universal property on the actual intrinsic complete subcategory.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The original ring-valued presentation of the actual coefficient limit.
Source: blueprint order 1261 (auxiliary; not a blueprint node). -/
abbrev pbcActualCompletedRing (T : Scheme.{u}) :=
  (adicLisseForget T).obj (pbcAdicCompletion T d)

/-- The recorded coefficient structure map, after forgetting commutativity.
Source: Stacks 099N (auxiliary; not a blueprint node). -/
abbrev pbcActualStructureMap : pbcActualCompletedRing d Y ⟶
    (proEtaleSheafDirectImage g RingCat.{u + 1}).obj (pbcActualCompletedRing d X) :=
  ⟨Functor.whiskerRight (completedCoefficientDirectImageMap g d).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

section CompletionPresentation
variable (X)
variable (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

attribute [local irreducible] pbcCompletedComparison

end CompletionPresentation

variable (T : Scheme.{u})

end AlgebraicGeometry.Scheme
