/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocal

/-!
# Finite étale morphisms split étale locally

Source: Stacks Project, Etale Morphisms, Lemma 04HN (lemma-finite-etale-etale-local)
(blueprint: lem-weil-pbc-finite-etale-etale-local-split)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite étale morphism `f : Y ⟶ X` is, around every point `x` of its target, a finite
disjoint union of copies of an étale neighbourhood: there are an étale `g : U ⟶ X`, a point
`u` over `x`, a finite `J` and open-and-closed pieces `ι j : V j ⟶ Y ×_X U` exhibiting
`Y ×_X U` as their coproduct (`IsColimit (Cofan.mk _ ι)`, the split-cover spelling of
lem-weil-pbc-direct-image-split-cover-product; the pieces are then pairwise disjoint and
cover), each mapping isomorphically to `U` under `pullback.snd`. Stacks Lemma 04HN
(blueprint: lem-weil-pbc-finite-etale-etale-local-split).

Proof (the five steps of the node):
1. An étale morphism is unramified; apply lem-weil-pbc-finite-unramified-etale-local
   (Stacks 04HJ) to `f` and `x`: an étale `g : U → X`, `u ↦ x`, a finite `J₀` and pairwise
   disjoint open and closed `V_j ⊆ Y_U` covering `Y_U` with each `p_j : V_j → U` a closed
   immersion.
2. `pr₂ : Y_U → U` is étale (base change), the inclusion of `V_j` is an open immersion, so
   `p_j` is an étale closed immersion, hence an open immersion
   (lem-weil-pbc-etale-closed-immersion-open) onto an open and closed `T_j ⊆ U`.
3. Shrink: `J = {j | u ∈ T_j}`, `U' = ⋂_{j ∈ J} T_j \ ⋃_{j ∉ J} T_j`, open with `u ∈ U'`;
   `g' = g ∘ ι` is étale with `g'(u) = x`.
4. `Y ×_X U'` is the open preimage `pr₂⁻¹(U')` (lem-weil-pbc-open-fibre-product and the
   universal property of the fibre product).
5. `V'_j = V_j ∩ pr₂⁻¹(U')` is empty for `j ∉ J` and maps isomorphically onto `U'` for
   `j ∈ J`; so `Y ×_X U' = ∐_{j ∈ J} V'_j` as claimed (`J = ∅` allowed when `Y_x = ∅`). -/
theorem finite_etale_etale_local_split {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Etale f] (x : X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
      Etale g ∧ g.base u = x ∧
      ∃ (J : Type u) (V : J → Scheme.{u}) (ι : ∀ j, V j ⟶ pullback f g),
        Finite J ∧
        Nonempty (IsColimit (Cofan.mk (pullback f g) ι)) ∧
        (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) ∧
        (∀ j : J, ∃ e : V j ≅ U, e.hom = ι j ≫ pullback.snd f g) := by
  sorry

end AlgebraicGeometry
