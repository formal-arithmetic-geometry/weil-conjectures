/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.RingedSiteLocalization
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Sheaf.CategoryTheory.RingedSiteLocalizationFractionComparison
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! The two-element localization exact sequence. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

/-- The localization at f + g has the standard two-open localization resolution.

Source: Stacks Project, algebraization.tex, Tag 0998, proof of
lemma-ideal-of-elements-complete-wrt, and Algebra, standard covering lemma.
(blueprint: lem-weil-pbc-ringed-localization-sum-sequence).

Proof: Put h = f + g. Sectionwise over W → U, in O(W)[1/h] the images of
f and g generate the unit ideal, since f/h + g/h = 1. The standard-covering
lemma gives injectivity and exactness in the middle of the diagonal and difference
sequence R → R[1/f] ⊕ R[1/g] → R[1/(fg)]. The last map is surjective:
write a fraction z/(fg)^n, with n positive. The binomial expansion of
(f/h + g/h)^(2n-1) yields u f^n + v g^n = 1 in R; the pair
(vz/f^n, -uz/g^n) maps to the fraction. These maps commute with restrictions.
Exact module sheafification preserves the short exact sequence. Universal
properties identify iterated localizations with product localizations. The
sequential-colimit model used here is the same localization: stage n sends x
to x/f^n, and the fraction relation gives the inverse. Thus the three sheaf
modules are precisely the ones displayed. The argument includes f + g = 0,
in which case all three terms are zero modules.
-/
theorem ringedSite_localization_sum_sequence
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C) (f g : R.obj.obj (op U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
    let L := fun t : R.obj.obj (op U) ↦ ringedSiteSectionLocalization R₀ U t
    ∃ (i : L (f + g) ⟶ L (f * (f + g)) ⊞ L (g * (f + g)))
      (p : L (f * (f + g)) ⊞ L (g * (f + g)) ⟶ L (f * g * (f + g)))
      (hip : i ≫ p = 0), (ShortComplex.mk i p hip).ShortExact := by sorry

end CategoryTheory
