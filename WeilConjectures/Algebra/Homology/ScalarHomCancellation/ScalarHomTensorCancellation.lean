/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Scalar tensor cancellation at independent coefficient universes

Source: Stacks Project, Modules on Sites, Tag 05V4, displayed tensor identity.
-/

@[expose] public section

universe u v r

open CategoryTheory MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules.ScalarHomCancellation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
attribute [local irreducible] monoidalCategory

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

attribute [local instance] isMonoidal_W_independentCoefficients

set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj E
set_option hygiene false in
local notation "𝓻" a =>
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a

attribute [local irreducible] cancellationApp cancellationPresheafIso

attribute [local irreducible] cancellationRestrictSheafifyHom cancellationRestrictSheafifyIso

attribute [local irreducible] cancellationTensorSheafifyIso

end SheafOfModules.ScalarHomCancellation
