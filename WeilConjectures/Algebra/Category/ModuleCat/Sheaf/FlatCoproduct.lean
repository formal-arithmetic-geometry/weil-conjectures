/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!
# Coproducts of flat sheaves of modules

## References

* Stacks Project, Modules on Sites, Lemma 18.28.5, Tag 03EU, clause (2)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- A set-indexed coproduct of flat sheaves of modules over a sheaf of commutative rings
is flat, including the empty coproduct. -/
theorem isFlat_coproduct
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) {B : Type u}
    (M : B → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hflat : ∀ b : B, IsFlat (M b)) : IsFlat (∐ M) := by
  let := monoidalCategory R
  let := symmetricCategory R
  have := isGrothendieckAbelian
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let := monoidalClosed (R := R)
  change exactFunctor _ _ (MonoidalCategory.tensorRight (∐ M))
  apply ObjectProperty.flat.tensorRight
  apply ObjectProperty.flat_coproduct M
  intro b
  have hb : exactFunctor _ _ (MonoidalCategory.tensorRight (M b)) := hflat b
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight (M b)) := hb.1
  apply (ObjectProperty.flat_iff_preservesFiniteLimits (M b)).2
  exact preservesFiniteLimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight (M b)).symm

end SheafOfModules
