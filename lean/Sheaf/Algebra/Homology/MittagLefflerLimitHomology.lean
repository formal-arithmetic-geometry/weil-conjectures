/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.CofilteredSystem
public import Sheaf.CategoryTheory.EssentiallyConstantSystem
import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels
import Sheaf.CategoryTheory.MittagLefflerExactSequence
import Sheaf.CategoryTheory.MittagLefflerLimitExact

/-!
# Homology of the limit of a Mittag-Leffler system of four-term complexes

Source: Stacks Project, Homology, Lemma 12.31.7, Tag 070E
(blueprint: lem-weil-pbc-mittag-leffler-complex-limit-homology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

/-- The canonical map from degree-zero cohomology of the limit complex to the limit of
its degree-zero cohomologies is an isomorphism (Stacks Project, Tag 070E).
(blueprint: lem-weil-pbc-mittag-leffler-complex-limit-homology)

The shape in the statement is the interval `0 → 1 → 2 → 3`: these indices represent
cochain degrees `-2, -1, 0, 1`. Its relation uses natural-number values, so there is no
arrow from `3` to `0`. Tower index `n : ℕ` represents the source's index `n + 1`.

Proof (Stacks, Tag 070E):
1. Put `Z_i^j = ker d_i^j` and `I_i^j = im d_i^{j-1}`. Commutation with transitions
   gives systems and the four short exact sequences involving these, the terms, and H.
2. Kernels commute with limits, so `ker d^0 = lim Z_i^0`.
3. The systems `I_i^{-1}` and `I_i^0` are ML as quotients of the two ML term systems
   (lem-weil-pbc-mittag-leffler-limit-exact, Tag 02N1(2)).
4. The short exact sequence `0 → I_i^{-1} → Z_i^{-1} → H_i^{-1} → 0` makes
   `Z_i^{-1}` ML since its quotient is essentially constant
   (lem-weil-pbc-exact-sequence-ml, Tag 070D).
5. Apply Tag 02N1(3) to `0 → Z_i^{-1} → A_i^{-1} → I_i^0 → 0` to get
   surjectivity on limits, hence `im d^{-1} = lim I_i^0`.
6. Left exactness (lem-weil-pbc-tower-limit-exact-surjective-kernels) and Tag 02N1(3)
   give `0 → lim I_i^0 → lim Z_i^0 → lim H_i^0 → 0`.
7. Quotienting the kernel in step 2 by the image in step 5 gives the asserted canonical
   isomorphism, sending the class of a compatible cycle family to its family of classes. -/
theorem isIso_limitPost_homology_of_mittagLeffler :
    let c : ComplexShape (Fin 4) :=
      { Rel := fun i j => i.val + 1 = j.val
        next_eq := fun h h' => Fin.ext (h.symm.trans h')
        prev_eq := fun h h' => Fin.ext (Nat.add_right_cancel (h.trans h'.symm)) }
    ∀ (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c),
      (K ⋙ eval AddCommGrpCat c 0 ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler →
      (K ⋙ eval AddCommGrpCat c 1 ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler →
      (K ⋙ homologyFunctor AddCommGrpCat c 1).IsEssentiallyConstant →
      IsIso (limit.post K (homologyFunctor AddCommGrpCat c 2)) := by
  sorry

end HomologicalComplex
