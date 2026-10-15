/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse

/-! # Lissity propagates through powers of a coefficient ideal

Source: Stacks Project, sites-cohomology.tex, Tag 094I, with Tag 094H
(blueprint: lem-weil-pbc-nilpotent-reduction-lissity).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Lissity of all cohomology sheaves after reduction modulo an ideal implies lissity
modulo every positive power, and implies lissity of the original object for a nilpotent
ideal. Source: Stacks Project, sites-cohomology.tex, Tags 094I and 094H
(blueprint: lem-weil-pbc-nilpotent-reduction-lissity).

Proof:
1. Locally constant finite-type module sheaves form a weak Serre subcategory
(`lem-weil-pbc-locally-constant-derived-serre`). Cohomology in that subcategory is closed
under distinguished triangles (`lem-sbc-cohomology-in-weak-serre-subcategory`).
2. Put Q_n = J^n/J^(n+1). The quotient short exact sequence gives a distinguished triangle
with terms K tensor Q_n, K tensor B/J^(n+1), and K tensor B/J^n. Exact sheafification
(`lem-weil-pbc-site-module-presheaf-sheafification-exact`) and a flat K-flat resolution
(`lem-pc-kflat-resolution`, `def-pc-flat-sheaf-modules`, `def-pc-kflat-complex`) compute
this triangle. Balancing identifies its first term with (K tensor B/J) tensor_(B/J) Q_n
using `lem-pur-derived-change-of-rings`.
3. B/J is Noetherian, and Q_n is finite over B/J because J^n is finitely generated.
Good truncation followed by `lem-pc-kflat-bounded-flat-replacement` and
`lem-pc-bounded-above-flat-kflat-site` shows that K tensor B/J is bounded above.
Tag 094H (`lem-weil-pbc-locally-constant-tensor`) makes the first triangle term lisse.
Induction and Step 1 make the middle term lisse over B. Quotient each local finite module
M by J^(n+1)M; exact sheafification preserves its constant sheaf since this ideal acts
as zero. This supplies the required quotient-linear local descriptions.
4. When J^m = 0, scalar extension identifies the reduction with K. On a K-flat model,
p tensor b maps to bp with inverse p maps to p tensor 1. Thus K has the same property. -/
theorem locallyConstantFiniteTypeModules_reduction_pow
    {C : Type u} [Category.{u} C] (T : Precoverage C)
    [T.HasIsos] [T.IsStableUnderComposition] [T.IsStableUnderBaseChange] [T.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B))]
    [∀ I : Ideal B, HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck (B ⧸ I)))]
    (K : DerivedCategory
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B)))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hmod : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck (Ideal.Quotient.mk J)).obj K))) :
    (∀ m : ℕ, 1 ≤ m →
      ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ m)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((constantCoefficientScalarExtension T.toGrothendieck
            (Ideal.Quotient.mk (J ^ m))).obj K))) ∧
    (∀ m : ℕ, 1 ≤ m → J ^ m = ⊥ →
      ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck B
        ((DerivedCategory.homologyFunctor _ i).obj K)) := by
  sorry

end SheafOfModules
