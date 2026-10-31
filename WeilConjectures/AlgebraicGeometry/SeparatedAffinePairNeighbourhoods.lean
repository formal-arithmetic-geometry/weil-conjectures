/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Separatedness from pairwise affine separated neighbourhoods

Source: Stacks Project, Tag 0AP6, paragraph following definition-ind-quasi-affine.
(blueprint: lem-a1-separated-affine-pair-neighbourhoods)

The terminal scheme is canonically isomorphic to `Spec ℤ` (using a universe lift).
No quasi-compactness assumption is imposed on the scheme or its witnessing opens.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A scheme is separated when every pair of affine opens lies in a separated open.

Source: Stacks Project, Tag 0AP6, paragraph following definition-ind-quasi-affine.
(blueprint: lem-a1-separated-affine-pair-neighbourhoods)

Proof plan:
1. Put `S = Spec ℤ` and `Y = X ×[S] X`, with projections `p,q`. For each pair of
   affine opens choose a separated witness `W`. By `lem-weil-pbc-open-fibre-product`,
   `W ×[S] W` is the open `p⁻¹(W) ∩ q⁻¹(W)`. These opens cover `Y`: choose affine
   neighbourhoods of the two projections of any point and then their witness.
   Take affine open covers of these open subschemes to obtain an affine cover of `Y`.
2. The inverse image of `W ×[S] W` under the diagonal is `W`, since both diagonal
   projections are identities. By `lem-weil-pbc-open-preimage-fibre-product` this
   identifies the pullback open subscheme. Uniqueness in `def-pc-fibre-product`
   identifies the restricted map with the diagonal of `W`, including its sheaf map.
3. Each witness diagonal is a closed immersion. Part (1) of
   `lem-weil-pbc-closed-immersion-affine-cover-criterion` gives affine preimages and
   surjective section maps on the chosen affine cover. Step 2 transfers these to
   the diagonal of `X`. Part (2) of that criterion makes this a closed immersion.
4. By `def-weil-proper-morphism` this says that `X` is separated. Apply
   `lem-pc-separated-quasi-separated` to its structure morphism to obtain
   quasi-separatedness. All covers may be infinite; no finite subcover is used.
-/
theorem separated_of_affine_pair_neighbourhoods (X : Scheme.{u})
    (h : ∀ A B : X.Opens, IsAffineOpen A → IsAffineOpen B →
      ∃ W : X.Opens, A ⊔ B ≤ W ∧ W.toScheme.IsSeparated) :
    IsClosedImmersion (pullback.diagonal (terminal.from X)) ∧
      X.IsSeparated ∧ QuasiSeparated (terminal.from X) := by
  sorry

end AlgebraicGeometry.Scheme
