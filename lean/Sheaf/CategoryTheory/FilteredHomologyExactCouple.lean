/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.CategoryTheory.ExactCouple
public import Sheaf.CategoryTheory.FilteredHomologyCoupleData

public import Sheaf.CategoryTheory.FilteredHomologyCoupleExactness

/-!
# The concrete filtered homology exact couple

Source: Stacks Project, Tags 012K and 011Q.
(blueprint: def-sp-filtered-homology-exact-couple).
-/

@[expose] public section

universe u v
namespace CategoryTheory

/-- Assemble the explicit homology terms and maps with their exactness proofs.
Source: Stacks Project, Tags 012K and 011Q.
(blueprint: def-sp-filtered-homology-exact-couple). -/
noncomputable abbrev filteredHomologyExactCouple {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) : BigradedExactCouple C 0 where
  D := filteredHomologyD K F
  E := filteredHomologyE K F
  alpha := filteredHomologyAlpha K F
  f := filteredHomologyF K F
  g := filteredHomologyG K F
  alpha_f_zero := (filteredHomologyCouple_exact C K F).1
  f_g_zero := (filteredHomologyCouple_exact C K F).2.1
  g_alpha_zero := (filteredHomologyCouple_exact C K F).2.2.1
  exact_alpha := (filteredHomologyCouple_exact C K F).2.2.2.1
  exact_f := (filteredHomologyCouple_exact C K F).2.2.2.2.1
  exact_g := (filteredHomologyCouple_exact C K F).2.2.2.2.2

/-- The reindexed initial E term is graded-piece homology.
Source: Stacks Project, Tag 012K.
(blueprint: def-sp-filtered-homology-exact-couple). -/
noncomputable def filteredHomologyEIso {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p q : ℤ) :
    ((filteredHomologyExactCouple K F).pageCouple 0).E (2 * p + q) (-p) ≅
      (F.gradedPiece p).homology (p + q) :=
  eqToIso (by
    change (F.gradedPiece (-(-p))).homology (2 * p + q + -p) =
      (F.gradedPiece p).homology (p + q)
    rw [neg_neg, show 2 * p + q + -p = p + q by omega])

end CategoryTheory
