/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Dimension

/-!
# Dimension of a scheme locally quasi-finite over an algebraic space

Source: Stacks Project, Decent Spaces, Tags 0ABW and 0A4J, and Properties of Spaces,
Tag 0BAN (blueprint: lem-sfb-space-quasifinite-source-dimension-bound).

Scheme tests express quasi-compactness of the relative diagonal. The locally quasi-finite
hypothesis uses representing pullback squares over every representable étale scheme chart.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A scheme locally quasi-finite over a quasi-separated algebraic space has topological
Krull dimension at most that of the space, including the empty and infinite-dimensional cases.
Source: Stacks Project, Decent Spaces, Tags 0ABW and 0A4J; Properties of Spaces, Tag 0BAN;
Properties, Tag 04MU (blueprint: lem-sfb-space-quasifinite-source-dimension-bound).

Proof:
1. By lem-sfb-space-topological-dimension-local-rings, quasi-separatedness gives
   `dim |X| = sup_x δ_X(x)`, where δ_X(x) is the dimension of the local ring at x,
   computed in an étale scheme chart. Hence every δ_X(x) is at most `dim |X|`.
2. For each u in U, apply lem-sfb-space-local-ring-dimension-quasifinite to f. The
   representing pullback squares in the hypothesis are exactly its chartwise hypothesis.
   It yields `dim O_{U,u} ≤ δ_X(f(u))`, and thus `dim O_{U,u} ≤ dim |X|`.
3. By lem-pc-scheme-dimension-local-rings, `dim |U| = sup_u dim O_{U,u}`. Taking the
   supremum in step 2 gives the claimed inequality. If U is empty this supremum is bottom.
   If X is empty, f forces U to be empty too. Infinite target dimension presents no exception.
No quasi-separatedness of U, global finite type, surjectivity, or Noetherianity is used. -/
theorem topologicalKrullDim_source_le_of_locallyQuasiFinite {S : Scheme.{u}}
    (X : AlgebraicSpace S) (U : Over S) (f : yoneda.obj U ⟶ X.obj.obj)
    (hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (hf : IsRepresentable f)
    (hqf : ∀ (V : Over S) (a : yoneda.obj V ⟶ X.obj.obj), IsEtale a →
      ∃ (W : Over S) (p : W ⟶ V) (q : yoneda.obj W ⟶ yoneda.obj U),
        IsPullback q (yoneda.map p) f a ∧ p.left.IsLocallyQuasiFinite) :
    topologicalKrullDim U.left ≤ topologicalKrullDim (Point X.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
