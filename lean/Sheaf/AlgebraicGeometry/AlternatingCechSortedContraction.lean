/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy

/-!
# AlternatingCechSortedContraction

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
(blueprint: lem-pc-alternating-cech-sorted-contraction)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The contraction boundary on a nondecreasing tuple.

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.2.
Proof: Stable sorting of a nondecreasing tuple is the identity. If the tuple is
strictly increasing, all faces are increasing and the repeated-tuple operator is
zero on the tuple and its faces. Otherwise let a be its first adjacent equality.
Expand the alternating differential and the sum duplicating the first repeat.
Deletions before a pair with face terms having first repeat a-1; deletions after
it pair with face terms having first repeat a. Their signs are opposite. The two
faces deleting the equal occurrences coincide and cancel, even if those faces
are increasing. The three deletions of the tripled value leave the original
tuple, with total coefficient (-1)^a*((-1)^a+(-1)^(a+1)+(-1)^(a+2))=1.
All restriction composites agree by uniqueness of the product map. Thus the
boundary equals the original section on repeated tuples and zero on increasing
tuples. In degree zero there is no repeated tuple and the operator is zero.
(blueprint: lem-pc-alternating-cech-sorted-contraction) -/
theorem cechSortedContraction (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F p) (t : Fin (p + 1) → I) (ht : Monotone t) :
    ((Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p) s t =
      s t - (if StrictMono t then s t else 0) := by sorry

end AlgebraicGeometry.Scheme
