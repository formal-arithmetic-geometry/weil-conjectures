/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators
import Sheaf.CategoryTheory.SiteCechComplex

/-!
# The outer faces of a duplicated first repeat

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.2.
(blueprint: lem-pc-alternating-cech-repeat-outer-faces)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The faces outside the tripled value cancel the incoming homotopy boundary.

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.2
and the verification omitted immediately after it.
Proof: Write q for duplication at a. For each deletion j<a from the duplicated tuple,
pair its term with deletion j from t followed by duplication at a-1. For each
j>a+2, pair with deletion j-1 from t followed by duplication at a. The resulting
tuples agree and their restriction composites agree, since Opens is a thin
category. The sign products differ by a factor -1. In the incoming differential,
the terms deleting a and a+1 have the same tuple and equal restrictions and
opposite signs, so cancel, regardless of where that face's first repeat lies.
Every other incoming term is one of the paired terms just described. Distribute
the finite sums and cancel these pairs.
(blueprint: lem-pc-alternating-cech-repeat-outer-faces) -/
theorem cechRepeatOuterFaces (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) (hp : 0 < p)
    (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I) (ht : Monotone t)
    (a : Fin (p + 2)) (ha : cechFirstRepeat t a) :
    let q := cechJunction (Equiv.refl _) (Equiv.refl _) a
    (∑ j : Fin (p + 3), if j.val < a.val ∨ a.val + 2 < j.val then
      ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ j.val) •
        F.map (S.indexMap t q).op
          (F.map (S.indexMap (t ∘ q) j.succAbove).op
            (s ((t ∘ q) ∘ j.succAbove))) else 0) = 
      -S.differentialValue F p ((cechSecondSortingHom X U F S p) s) t := by sorry

end AlgebraicGeometry.Scheme
