/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.Picard.MixedTensorPointwiseLeftDerived
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Derived tensor with a fixed complex in the second factor

Source: Stacks Project, More on Algebra, Tags 064L and 06Y6 and Section 06Y5
(blueprint: lem-pc-derived-tensor-second-factor-functor).

The tensor bifunctor is the landed mixed module tensor, totalized in the order `(E, N)`.
Thus the differential is `d_E ⊗ 1 + (-1)^p 1 ⊗ d_N`, and the `A`-action comes from `N`.
K-flatness uses the landed ordinary-module specialization of the ringed-site notion.
-/

@[expose] public section

universe u wR wA

open CategoryTheory

namespace DerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{u} A)]

set_option quotPrecheck false in
local notation "QR" => (Q : CochainComplex (ModuleCat R) ℤ ⥤
  DerivedCategory (ModuleCat R))
set_option quotPrecheck false in
local notation "QA" => (Q : CochainComplex (ModuleCat A) ℤ ⥤
  DerivedCategory (ModuleCat A))
set_option quotPrecheck false in
local notation "W" => HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)

end DerivedCategory
