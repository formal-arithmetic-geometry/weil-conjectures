/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix

/-!
# Independence of the corank of a local presentation

Source: the geometric evaluation step of the rank/descent argument accompanying
Hemo--Richarz--Scholbach, Example 3.1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Two finite presentations of the same pulled-back module have equal coranks over
points with the same image. No noetherian hypothesis is needed here.
Source: the rank/descent argument, step 3, accompanying Hemo--Richarz--Scholbach,
Example 3.1; Bhatt--Scholze, Example 4.2.11
(blueprint: lem-weil-pbc-condensed-field-presentation-corank).
Proof: choose an algebraic closure of a common overfield of the two residue fields
at v and w over the residue field of their common image. The resulting geometric
point factors through both cover members. Pull back both cokernel presentations to
that geometric point. Inverse image is additive and preserves finite colimits, and
the monoidal coefficient comparison sends the regular module to the regular module.
Evaluation at the final object on the algebraically closed field is exact, because
pro-etale covers there split, and sends the coefficient ring to E. Compatibility of
the canonical continuous-function realization with inverse image identifies the two
maps with their evaluated matrices. Both cokernels therefore compute the same finite
dimensional E-vector space. Rank-nullity gives n minus matrix rank for both of its
dimensions. This includes zero rows, zero columns, and zero-dimensional cokernels.
An empty cover member contributes no points. -/
theorem condensedField_presentation_corank_eq
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (n m : C.I₀ → ℕ)
    (f : ∀ i, Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)) (m i) ⟶
      Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)) (n i))
    (e : ∀ i, (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P) ≅ cokernel (f i))
    (i j : C.I₀) (v : C.X i) (w : C.X j) (h : C.f i v = C.f j w) :
    n i - ((continuousFieldPresentationMatrix E (C.X i)
      (condensedFieldPullbackRealization E (C.f i)) (f i)).map (fun a ↦ a v)).rank =
    n j - ((continuousFieldPresentationMatrix E (C.X j)
      (condensedFieldPullbackRealization E (C.f j)) (f j)).map (fun a ↦ a w)).rank := by sorry

end AlgebraicGeometry.ProEtale
