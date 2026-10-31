/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-! # K-flat resolutions without identifying the site universes

Source: Stacks Project, Cohomology on Sites, Tag 06YS
(blueprint: lem-pc-kflat-resolution).
-/

@[expose] public section

universe r u v w

open CategoryTheory MonoidalCategory Limits Opposite
open scoped ZeroObject

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  {M P N : PresheafOfModules.{r} (R ⋙ forget₂ _ _)}

private local instance small_hom_kfi {S : Cᵒᵖ ⥤ RingCat.{r}}
    (M N : PresheafOfModules.{r} S) : Small.{r} (M ⟶ N) := by
  have := locallySmall_kfi.{r, u, v} (S := S)
  infer_instance

private local instance essentiallySmall_over_kfi (X : C) : EssentiallySmall.{r} (Over X) :=
  CostructuredArrow.essentiallySmall (S := 𝟭 C) (T := X)

omit [EssentiallySmall.{r} C] in
private local instance small_homObj_kfi (M N : PresheafOfModules.{r} (R ⋙ forget₂ _ _))
    (X : Cᵒᵖ) : Small.{r} ((homObj M N).obj X) :=
  small_hom_kfi _ _

variable (M) in
omit [EssentiallySmall.{r} C] in
omit [EssentiallySmall.{r} C] in
omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
variable (M N) in
omit [EssentiallySmall.{r} C] in
end PresheafOfModules

namespace SheafOfModules

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

-- The sheafification functor from presheaves of modules over `R` to sheaves of modules over `R`.
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{r} (𝟙 (𝓡).obj)

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]

attribute [local instance] isMonoidal_W_independentCoefficients
  monoidalCategory symmetricCategory

set_option maxHeartbeats 1000000 in
-- The tensor localization comparison has dependent sheafification instances.
end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "O" => (sheafCompose J
  (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{r} O

attribute [local instance] isMonoidal_W_independentCoefficients
  monoidalCategory symmetricCategory monoidalClosed_kfi

private theorem monoidalPreadditive_kfi : MonoidalPreadditive A := by
  have (M : A) : (tensorLeft M).Additive := by
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := inferInstance
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

end SheafOfModules

namespace CochainComplex

set_option synthInstance.maxSize 1024 in
end CochainComplex
