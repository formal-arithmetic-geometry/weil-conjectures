/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Separated étale charts of algebraic spaces

Source: Stacks Project, `spaces-properties.tex`, Tag 03FZ and
`morphisms.tex`, Tag 01QR (blueprint: lem-a1-separated-etale-chart).

The representable diagonal is expressed by the closed-immersion property
of every scheme test; the second clause records a scheme representing each
scheme fibre product and the separatedness of its projection.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated scheme étale chart into an algebraic space has separated
representable diagonal, and all its scheme fibre products over the space are
separated.

Source: Stacks Project, `spaces-properties.tex`, Tag 03FZ (lemma-separated-cover),
and `morphisms.tex`, Tag 01QR (base change of closed immersions); the scheme
cancellation input is `schemes.tex`, Tag 01KV.
(blueprint: lem-a1-separated-etale-chart)

Proof: absolute separatedness of `U` and separated cancellation give a closed
immersion for the diagonal of `U` over `S`.  The diagonal of the chart is its
base change along the represented relation `U ×_E U`, so closed-immersion base
change gives the first clause, including all scheme tests.  For a scheme `C`
with a map to `E`, represent `C ×_E U` by a scheme `W`; the same cartesian
diagonal argument identifies its diagonal over `C` as a base change of the
chart diagonal, proving the second clause.
-/
theorem separated_etale_chart
    {S : Scheme.{u}} (E : AlgebraicSpace S) (U : Over S)
    [Scheme.IsSeparated U.left]
    (u : yoneda.obj U ⟶ E.obj.obj) (hu : IsEtale u) :
    AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (CategoryTheory.Limits.pullback.lift (𝟙 (yoneda.obj U)) (𝟙 (yoneda.obj U))
        (by simp) : yoneda.obj U ⟶ CategoryTheory.Limits.pullback u u) ∧
      ∀ (C : Over S) (c : yoneda.obj C ⟶ E.obj.obj),
        ∃ (W : Over S) (p : W ⟶ C) (q : yoneda.obj W ⟶ yoneda.obj U),
          IsPullback q (yoneda.map p) u c ∧ IsSeparated p.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
