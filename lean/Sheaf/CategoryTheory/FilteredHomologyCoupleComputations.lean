/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence

/-! # Computation rules for the concrete filtered homology couple

Source: Stacks Project, Tag 012K, the homology exact couple of filtration steps.
-/

@[expose] public section

universe u v
namespace CategoryTheory

/-- The D objects and normalized initial G maps have their concrete formulas.
Source: Stacks Project, Tag 012K, the homology exact-couple construction.
(blueprint: lem-sp-filtered-homology-couple-computations).

Proof. The D field of the assembled couple is filteredHomologyD. Expanding
this abbreviation gives the first equality at every pair of integer indices.
For the second formula, expand initialG, which changes only its target index at type zero.
The G field of the concrete couple is filteredHomologyG, namely the homology
map of the filtration-step quotient. The initial E isomorphism transports
the graded-piece and homological degree indices back to p and p+q. Cancel
the equality transports, using -(-p)=p and 2*p+q-p=p+q. The resulting maps
are identical, giving the displayed heterogeneous equality. -/
theorem filteredHomologyExactCouple_computations
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    (∀ P Q : ℤ, (filteredHomologyExactCouple K F).D P Q =
      (F.step (-Q) : CochainComplex C ℤ).homology (P + Q)) ∧
    (∀ p q : ℤ, ((filteredHomologyExactCouple K F).initialG (2 * p + q) (-p) ≫
        (filteredHomologyEIso K F p q).hom) ≍
      HomologicalComplex.homologyMap
        (F.complexQuotientπ p (p + 1) (by omega)) (p + q)) := by
  constructor
  · intros
    rfl
  · intro p q
    simp only [filteredHomologyEIso, eqToIso.hom, BigradedExactCouple.initialG,
      filteredHomologyExactCouple, filteredHomologyG, comp_eqToHom_heq_iff]
    have h (a n a' n' : ℤ) (ha : a = a') (hn : n = n') :
        HomologicalComplex.homologyMap (F.complexQuotientπ a (a + 1) (by omega)) n ≍
          HomologicalComplex.homologyMap (F.complexQuotientπ a' (a' + 1) (by omega)) n' := by
      subst a' n'
      rfl
    exact h (-(-p)) (2 * p + q + -p) p (p + q) (by omega) (by omega)


end CategoryTheory
