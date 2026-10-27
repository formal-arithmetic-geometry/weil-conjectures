/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.AlgebraicTopology.SimplicialAbelianHornFilling
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Compatible boundaries in acyclic simplicial abelian groups

Source: Stacks Project, Simplicial, Tag 08P1, `lemma-qis-simplicial-abelian-groups`,
third proof paragraph, using Tag 08NZ, `lemma-simplicial-group-kan`
(blueprint: lem-trf-simplicial-normalized-acyclic-compatible-boundary).

Mathlib's normalized Moore complex uses the intersection of the positive-face kernels
and the differential induced by face zero. The simplex dimension below is `n + 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- Acyclicity of the normalized Moore complex fills every compatible boundary.
Source: Stacks Project, Simplicial, Tag 08P1, `lemma-qis-simplicial-abelian-groups`,
third proof paragraph, with face zero omitted in the initial horn; Tag 08NZ
(blueprint: lem-trf-simplicial-normalized-acyclic-compatible-boundary).

The acyclicity hypothesis includes degree zero: the differential out of that term is
zero, so every degree-zero element is a normalized boundary. For `n = 0` the simplex
has dimension one and compatibility imposes no equations. In higher dimensions an
ordered pair of distinct boundary indices is `i.castSucc < j.succ`, encoded by `i ≤ j`.

Proof, following the four DAG steps:
1. Discard face zero and use `lem-trf-simplicial-abelian-horn-filling` with missing
   index zero to obtain `u` with the prescribed positive faces. Set `r = a₀ - d₀u`.
2. In dimension at least two, the face-face identity
   `lem-weil-pbc-simplex-face-face-identity`, applied contravariantly using
   `def-weil-pbc-simplicial-object`, gives `dⱼd₀ = d₀dⱼ₊₁`.
   Boundary compatibility gives `dⱼa₀ = d₀aⱼ₊₁`. Additivity therefore gives
   `dⱼr = d₀aⱼ₊₁ - d₀dⱼ₊₁u = 0` for every face of `r`.
   Thus `r` belongs to the normalized term and is a cycle.
3. In dimension one, `r` lies in degree zero, whose outgoing differential is zero;
   it is a cycle without any compatibility condition or a face out of degree zero.
4. Exactness in the degree of `r` supplies a normalized element `w` with `d₀w = r`.
   Its positive faces vanish. By additivity, `v = u + w` has face zero `a₀` and
   all positive faces `aᵢ`, as required. -/
theorem exists_boundary_filler_of_normalized_acyclic
    (G : SimplicialObject AddCommGrpCat.{u})
    (hacyclic : ((AlgebraicTopology.normalizedMooreComplex AddCommGrpCat).obj G).Acyclic)
    (n : ℕ) (a : Fin (n + 2) → G _⦋n⦌)
    (hcompat : match n, a with
      | 0, _ => True
      | m + 1, a => ∀ (i j : Fin (m + 2)), i ≤ j →
          G.δ i (a j.succ) = G.δ j (a i.castSucc)) :
    ∃ v : G _⦋n + 1⦌, ∀ i : Fin (n + 2), G.δ i v = a i := by
  sorry

end CategoryTheory.SimplicialObject
