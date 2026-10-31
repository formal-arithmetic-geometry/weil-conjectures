/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # Constant scalars in an algebraic inverse-image lift

Source: Stacks Project, Tags 00YV and 03D2; the constant-coefficient calculation
in Step 2 of lem-sf-constant-open-restriction-model-comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ConstantCompletion

private noncomputable abbrev ringSets {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :=
  sheafCompose J (forget CommRingCat.{u})

private noncomputable abbrev scalar {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    (F : InverseImageData L) (A : Type u) [CommRing A] :=
  (F.algebra (constant J A)).ringUnderlying.hom ≫ (ringSets K).map (constantMap F A)

end CategoryTheory.ConstantCompletion
