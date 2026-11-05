/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Category.Grp.AB

/-! # K-flat resolutions without identifying the site universes

Source: Stacks Project, Cohomology on Sites, Tag 06YS
(blueprint: lem-pc-kflat-resolution).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Limits Opposite
open scoped ZeroObject

namespace PresheafOfModules

open Opposite

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}

end PresheafOfModules

namespace SheafOfModules

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R

-- The sheafification functor from presheaves of modules over `R` to sheaves of modules over `R`.
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{max u v} (𝟙 (𝓡).obj)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  {R : Sheaf J CommRingCat.{max u v}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] [HasWeakSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] monoidalCategory symmetricCategory

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
local notation "O" => (sheafCompose J
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{max u v} O

attribute [local instance] monoidalCategory symmetricCategory monoidalClosed_kfg

end SheafOfModules

namespace CochainComplex

end CochainComplex
