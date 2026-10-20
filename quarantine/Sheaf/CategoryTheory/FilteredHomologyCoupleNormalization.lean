/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
import Sheaf.CategoryTheory.FilteredHomologyCoupleData
import WeilConjectures.CategoryTheory.ExactCoupleConvergence

/-! # Normalization of the concrete filtered homology couple

Source: Stacks Project, Tags 012K, 011Q and 0AMK, the initial homology exact couple.
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- The D terms and the two homology maps of the explicit filtered couple.
Source: Stacks Project, Tags 012K, 011Q and 0AMK, the initial homology exact couple.
(blueprint: lem-sp-filtered-homology-couple-normalization).

Proof. The D terms of the concrete couple are exactly filtration-step homology,
so take the identity isomorphisms eD. Its alpha map is defined as homology of
the filtration inclusion, followed by the equality of the homology degrees;
this is the first equation. Its initialG is the homology map of the quotient
projection followed by the equality identifying its type-zero target. The
isomorphism filteredHomologyEIso is the equality isomorphism at the reindexed
bidegree. In the second equation all equality morphisms compose to the identity:
2(-Q)+(P+2Q)=P, -(-Q)=Q and -Q+(P+2Q)=P+Q. Thus only homology of the quotient
projection remains. This computation applies to arbitrary, including zero or
constant, filtrations and uses no finite-filtration hypothesis. -/
theorem filteredHomologyCouple_normalization
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    ∃ (eD : ∀ P Q : ℤ, (filteredHomologyExactCouple K F).D P Q ≅
        (F.step (-Q) : CochainComplex C ℤ).homology (P + Q)),
      (∀ P Q : ℤ,
        (filteredHomologyExactCouple K F).alpha P Q ≫
            (eD (P - 1) (Q + 1)).hom =
          (eD P Q).hom ≫ HomologicalComplex.homologyMap
            (Subobject.ofLE (F.step (-Q)) (F.step (-(Q + 1)))
              (F.antitone_step (by omega))) (P + Q) ≫
            eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) ∧
      (∀ P Q : ℤ,
        (filteredHomologyExactCouple K F).initialG P Q ≫
            eqToHom (by congr 1 <;> omega) ≫
            (filteredHomologyEIso K F (-Q) (P + 2 * Q)).hom ≫
            eqToHom (by
              rw [show -Q + (P + 2 * Q) = P + Q by omega]
              rfl) =
          (eD P Q).hom ≫ HomologicalComplex.homologyMap
            (F.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q)) := by
  sorry

end CategoryTheory
