/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.LinearAlgebra.IdempotentCharpoly
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.LinearAlgebra.IdempotentImageBaseChange
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover

/-! # Local matrix realization of an idempotent summand determinant

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph.
(blueprint: lem-weil-pbc-idempotent-charpoly-local-charpoly)
-/

@[expose] public section

universe u v

namespace Matrix

/-- On a finite standard cover, the summand determinant is a matrix characteristic polynomial.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph;
the determinant realization and the refinement argument are made explicit here.
(blueprint: lem-weil-pbc-idempotent-charpoly-local-charpoly)

Proof: reindex the ambient free module by `Fin (Fintype.card n)`. The image-base-change
lemma applied to P and 1-P splits it into their finite projective images. Choose finite
standard free covers for these two images using the finite-projective cover theorem.
Refine the covers by all pairwise products of their elements: multiplying expressions
for 1 in the two generated ideals shows that these products still span the unit ideal.
Localization at a product factors through either localization, so both summands are
finite free there, and their split decomposition is preserved by base change. Choose
finite bases of both summands and concatenate them to a basis of the ambient module.
The equation TP=PT shows that T preserves the summands. In this basis P is diag(1,0)
and T is diag(U,V), where U has size d, the rank of the first summand. Consequently
1-P+(X-T)P is diag(X-U,1). Ring maps commute with the determinant and with the displayed
polynomial matrix operations; conjugation preserves determinant. The determinant of
this block diagonal matrix is U.charpoly times det(1), which is U.charpoly. Enumerate
the finite product cover by Fin r and use these U as the existential witnesses.
No constant-rank assumption is needed: d may vary over the cover. Over the zero ring,
a one-element cover with f=1 and d=0 works, since all polynomial equalities hold.
For an empty ambient index set the determinant is 1, realized by the empty matrix.
-/
theorem exists_standardCover_idempotentCharpoly_eq_charpoly
    {A : Type u} [CommRing A] {n : Type v} [Fintype n] [DecidableEq n]
    (T P : Matrix n n A) (hP : P * P = P) (hTP : T * P = P * T) :
    ∃ (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = ⊤ ∧
      ∀ i : Fin r, ∃ (d : ℕ) (U : Matrix (Fin d) (Fin d) (Localization.Away (f i))),
        (idempotentCharpoly T P).map (algebraMap A (Localization.Away (f i))) =
          U.charpoly := by sorry

end Matrix
