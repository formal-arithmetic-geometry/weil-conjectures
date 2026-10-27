/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.GroupScheme.Image
import Sheaf.AlgebraicGeometry.AbelianVariety.HomImageDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# The equal-dimension isogeny criterion

Source: Milne, Abelian Varieties, Chapter I, Proposition 7.1 (a) iff (b), printed p.32,
and its proper-image argument (blueprint: lem-sfb-equal-dimension-isogeny-criterion).

## Main statements

- `AlgebraicGeometry.isIsogeny_iff_surjective_of_topologicalKrullDim_eq`: a homomorphism
  between equal-dimensional abelian varieties is an isogeny exactly when it is surjective.
- `AlgebraicGeometry.not_isDominant_of_not_isIsogeny`: an endomorphism of an abelian variety
  which is not an isogeny is not dominant.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A homomorphism between equal-dimensional abelian varieties over any field is an
isogeny if and only if it is surjective on underlying scheme points.

Source: Milne, Abelian Varieties, Chapter I, Proposition 7.1 (a) iff (b), printed p.32
(blueprint: lem-sfb-equal-dimension-isogeny-criterion).

Proof:
1. An isogeny is surjective by `def-sc-isogeny`, implemented by `IsIsogeny`.
2. Conversely, suppose the homomorphism is surjective. By `lem-sc-image-subgroup`,
   its scheme-theoretic image I is a closed subgroup and the map onto I is surjective:
   the source is proper and the target separated and finite type by
   `def-sc-abelian-variety`. The inclusion I into B is surjective on points, hence a
   homeomorphism by `def-weil-closed-immersion`, so dim I = dim B. The formula in
   `lem-sfb-abelian-hom-image-dimension` is dim A = dim I + dim ker f. The dimensions
   of A and I are finite by `lem-kun-dimension-finite-type`. The kernel is nonempty
   because it contains the identity (`def-sc-group-scheme`). Cancel the common finite
   dimension using dim A = dim B to obtain dim ker f = 0.
3. The kernel is a closed subgroup by `lem-sc-kernel-subgroup`. Apply
   `lem-pc-zero-dimensional-closed-subscheme-finite` to this closed subscheme of A.
   Its structure morphism is finite, so f is an isogeny by `def-sc-isogeny`.
   This uses the scheme-theoretic kernel, without a reducedness or separability assumption. -/
theorem isIsogeny_iff_surjective_of_topologicalKrullDim_eq
    {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [GrpObj A] [GrpObj B] [IsAbelianVariety A] [IsAbelianVariety B]
    (h_dim : topologicalKrullDim A.left = topologicalKrullDim B.left)
    (f : A ⟶ B) [IsMonHom f] :
    IsIsogeny f ↔ Surjective f.left := by
  sorry

/-- An endomorphism of an abelian variety which is not an isogeny is not dominant.

Source: Milne, Abelian Varieties, Chapter I, Proposition 7.1, printed p.32, its
proper-image argument (blueprint: lem-sfb-equal-dimension-isogeny-criterion).

Proof: By `lem-weil-pbc-proper-to-separated`, the endomorphism is proper: the structure
morphism of A is proper and separated by `def-sc-abelian-variety`. Its image is closed by
`lem-weil-pbc-proper-closed-image`. If it were dominant, its image would also be dense,
hence all of A. Apply `isIsogeny_iff_surjective_of_topologicalKrullDim_eq` with B = A and
the reflexive dimension equality. It would be an isogeny, contradicting the hypothesis. -/
theorem not_isDominant_of_not_isIsogeny
    {k : Type u} [Field k] {A : Over (Spec (.of k))}
    [GrpObj A] [IsAbelianVariety A] (f : A ⟶ A) [IsMonHom f]
    (hf : ¬ IsIsogeny f) : ¬ IsDominant f.left := by
  sorry

end AlgebraicGeometry
