/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.RingTheory.MPseudoCoherent
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.RingTheory.DerivedMapLift

/-!
# Pseudo-coherence in distinguished triangles

Source: Stacks Project, `more-algebra.tex`, Tag 064R,
`more-algebra-lemma-cone-pseudo-coherent`
(blueprint: lem-pc-ring-pseudo-coherent-distinguished-triangle).
-/

@[expose] public section

universe u v w

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory (IsMPseudoCoherent)

namespace CategoryTheory

/-- The three two-out-of-three assertions for `m`-pseudo-coherence
(the landed `DerivedCategory.IsMPseudoCoherent` of node def-pc-ring-m-pseudo-coherent).

Source: Stacks Project, `more-algebra.tex`, Tag 064R,
`lemma-cone-pseudo-coherent` (blueprint: lem-pc-ring-pseudo-coherent-distinguished-triangle).

Proof, first clause: choose bounded finite-free witnesses `P ⟶ A` at `m + 1`
and `E ⟶ B` at `m`. Brutally truncate `P` below `m + 1`; the witness conditions
are unchanged. Apply `lem-pc-ring-derived-map-lift` (Stacks Tag 064E) at `n = m`
to lift `P ⟶ A ⟶ B` through `E ⟶ B` to a chain map `γ : P ⟶ E`.
The cone `Q` of `γ` is bounded finite free. The commuting square extends by TR3
(`def-weil-triangulated-category`) to a morphism from the cone triangle to `T`.
Use the long exact cohomology sequences (`lem-sf-derived-homology-long-exact`)
and their commutative ladder (`lem-weil-pbc-derived-cohomology-ladder`).
For `i > m`, in the five terms `Hⁱ(P), Hⁱ(E), Hⁱ(Q), Hⁱ⁺¹(P), Hⁱ⁺¹(E)`,
the first vertical map is surjective and the second, fourth and fifth are
isomorphisms; `lem-weil-pbc-five-lemma` makes the third an isomorphism.
At `i = m`, the four terms `Hᵐ(E), Hᵐ(Q), Hᵐ⁺¹(P), Hᵐ⁺¹(E)` have surjective
first and third vertical maps and an injective fourth map. Apply
`lem-pc-four-lemma-epi` to obtain surjectivity on `Hᵐ(Q) ⟶ Hᵐ(C)`.
Thus `Q ⟶ C` is the required witness.

For the second clause rotate twice to `C ⟶ A[1] ⟶ B[1] ⟶ C[1]` and apply
the first clause at `m - 1`. Since `Hⁱ(A[1]) = Hⁱ⁺¹(A)`, shifting back gives
`m`-pseudo-coherence of `B`. For the third clause rotate once to
`B ⟶ C ⟶ A[1] ⟶ B[1]`, apply the first clause at `m`, and shift back.
Rotation preserves distinguished triangles by `def-weil-abstract-derived-category`. -/
theorem isMPseudoCoherent_of_distinguished_triangle
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ)
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} R))) :
    (IsMPseudoCoherent (m + 1) T.obj₁ →
        IsMPseudoCoherent m T.obj₂ → IsMPseudoCoherent m T.obj₃) ∧
      (IsMPseudoCoherent m T.obj₁ →
        IsMPseudoCoherent m T.obj₃ → IsMPseudoCoherent m T.obj₂) ∧
      (IsMPseudoCoherent (m + 1) T.obj₂ →
        IsMPseudoCoherent m T.obj₃ → IsMPseudoCoherent (m + 1) T.obj₁) := by
  sorry

end CategoryTheory
