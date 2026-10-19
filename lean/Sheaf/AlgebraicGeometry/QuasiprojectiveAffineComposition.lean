/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product

/-!
# Composition of finite projective-space immersions over an affine base

Source: Stacks Project, Morphisms, Tags 0C4M and 01VT; the direct proof uses Constructions,
Tags 01NF and 01WD, and Schemes, Tags 01JY and 02V0
(blueprint: lem-per-quasiprojective-affine-composition).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Over the spectrum of a commutative Noetherian ring, the composite of two finite-type
morphisms admitting immersions into finite-dimensional projective spaces over their targets
again admits such an immersion. Here a locally closed immersion is `IsImmersion`, equivalent
to a closed immersion followed by an open immersion by `IsImmersion.isImmersion_iff_exists`.
The coordinate type `ULift (Fin (n + 1))` represents classical projective dimension `n`.

Source: Stacks Project, Morphisms, Tags 0C4M and 01VT
(blueprint: lem-per-quasiprojective-affine-composition).

Proof (the node's direct Segre argument):
1. Choose the dimensions `a`, `b` and immersions `i : X ⟶ ℙ^a_Y`, `j : Y ⟶ ℙ^b_S`
   from the hypotheses, with their projection identities. The projective spaces are those
   of def-nagata-projective-space-base-change; immersion has the meaning of
   def-weil-closed-immersion.
2. Use lemma-nagata-projective-space-base-change-pullback, namely
   `ProjectiveSpace.isPullback_map`, to identify `ℙ^a_Y` with `Y ×_S ℙ^a_S`.
   The fibre-product universal property (def-pc-fibre-product) gives
   `k : ℙ^a_Y ⟶ ℙ^b_S ×_S ℙ^a_S` by pairing `j` after projection with the map to `ℙ^a_S`.
   Its square over `j` is cartesian: a compatible pair into `Y` and the product determines
   the unique pair into `Y ×_S ℙ^a_S`, and both product projections verify its image.
   Thus `k` is an immersion by lem-weil-pbc-immersion-base-change-lft, clause (1).
3. Compose `i` with `k` using lem-weil-pbc-proper-fp-permanence, clause (e).
   The projection identities show that this immersion into the product lies over `f ≫ g`.
4. Apply the binary relative Segre closed immersion of lem-chow-segre, with dimensions `b,a`.
   Its target has dimension `(b + 1) * (a + 1) - 1 = a*b + a + b`.
   A closed immersion is an immersion, and clause (e) of lem-weil-pbc-proper-fp-permanence
   composes it with the previous immersion. The Segre morphism is over `S`, so the resulting
   projection is still `f ≫ g`. -/
theorem exists_isImmersion_projectiveSpace_comp_of_affine
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    (hf : ∃ (a : ℕ) (i : X ⟶ ProjectiveSpace (ULift.{u} (Fin (a + 1))) Y),
      IsImmersion i ∧ i ≫ (ProjectiveSpace (ULift.{u} (Fin (a + 1))) Y ↘ Y) = f)
    (hg : ∃ (b : ℕ)
      (j : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (b + 1))) (Spec (.of R))),
      IsImmersion j ∧
        j ≫ (ProjectiveSpace (ULift.{u} (Fin (b + 1))) (Spec (.of R)) ↘ Spec (.of R)) = g) :
    ∃ (N : ℕ) (i : X ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))),
      IsImmersion i ∧
        i ≫ (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R)) ↘ Spec (.of R)) =
          f ≫ g := by
  sorry

end AlgebraicGeometry
