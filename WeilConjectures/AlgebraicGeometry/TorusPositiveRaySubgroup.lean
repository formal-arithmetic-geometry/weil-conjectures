/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TorusCharacterTangentWeights
public import WeilConjectures.AlgebraicGeometry.SolvableGroupStructure
public import Mathlib.Topology.Connected.Basic

/-! # The subgroup attached to a positive ray of torus characters

Source: Milne, Algebraic Groups (2017), Proposition 16.64 and its uniqueness
sentence, pp.348--349; unipotence also follows from Proposition 16.62, pp.346--347
(blueprint: lem-sfb-torus-positive-ray-subgroup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.TorusCharacterTangent

/-- A positive ray in the character lattice integrates to a unique smooth connected
stable unipotent closed subgroup, with both tangent-space inclusion comparisons.
Source: Milne, Proposition 16.64 and its following uniqueness sentence, pp.348--349
(blueprint: lem-sfb-torus-positive-ray-subgroup).

Proof plan:
1. Identify the character lattice by `lem-sfb-multiplicative-character-antiduality`.
   Apply `lem-sfb-pid-submodule-smith-bases` to Zeta to choose coordinates with
   eta = dε₁, d > 0. Let T be the coordinate subtorus t₁ = 1 and λ(t) = (t,1,...,1).
   A character trivial on T lies on the positive eta-ray precisely when its λ-weight
   is positive.
2. Successively apply `lem-sfb-gm-representation-weight-basis` to the commuting
   coordinate factors. The positive λ-part of h^T is Veta, and that of k^T is
   k ∩ Veta. These are character weights, including in positive characteristic.
3. Form H semidirect S with its explicit product group law. Smoothness follows
   from `lem-trf-split-lattice-torus-projection` and `lem-trf-smooth-composition`;
   connectedness follows from the geometrically connected split torus and
   `lem-weil-pbc-geometrically-connected-product-components`. It is affine and
   finite type. The same holds with any smooth connected stable K in place of H.
4. Apply `lem-sfb-torus-centralizer-smooth-connected` to T in the semidirect
   product. On every test algebra its centralizer is H^T semidirect S. Its Lie
   algebra is h^T plus Lie(S); λ acts trivially on the second summand.
5. Apply `lem-sfb-cocharacter-limit-smooth-structure` to this centralizer and λ.
   Its contracting subgroup U is smooth connected unipotent and closed; the limit
   condition forces its projection to S to be 1, so U lies in H. Its tangent space
   is Veta. Commutation with S makes U stable. For K the same construction gives
   U_K inside both K and U, with tangent space k ∩ Veta.
6. If Veta lies in k, the inclusion U_K → U has bijective differential and positive
   source tangent weights. `lem-sfb-positive-weight-equivariant-inverse` makes
   it an isomorphism, proving U lies in K.
7. If k lies in Veta, apply the same inverse criterion to U_K → K, proving K lies
   in U. The criterion permits an empty set of tangent weights.
8. If a smooth connected stable closed subgroup has tangent space Veta, both
   comparisons give equality as a closed subgroup, hence the unique isomorphism
   commuting with the inclusions. This also covers Veta = 0. -/
theorem exists_torus_positiveRay_subgroup
    (F : Type u) [Field F] [IsAlgClosed F]
    (H S : Grp (Over (Spec (.of F))))
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (r : ℕ) (hS : Nonempty (S ≅ MultiplicativeType.splitTorus F r))
    [ModObj S.X H.X] (hAut : ActsByGroupAutomorphisms S H)
    (eta : S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (heta : eta.hom.hom ≠ 1) :
    ∃ (U : Grp (Over (Spec (.of F)))) (i : U ⟶ H),
      IsClosedSubgroupScheme i.hom.hom ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
      SolvableGroupStructure.IsUnipotent U ∧ IsStable S H i ∧
      (GrpObj.differential i.hom.hom).toLinearMap.range = positiveRaySpace S H eta ∧
      (∀ (K : Grp (Over (Spec (.of F)))) (j : K ⟶ H),
        IsClosedSubgroupScheme j.hom.hom → Smooth K.X.hom → ConnectedSpace K.X.left →
        IsStable S H j →
          (positiveRaySpace S H eta ≤ (GrpObj.differential j.hom.hom).toLinearMap.range →
            ∃ f : U ⟶ K, f ≫ j = i) ∧
          ((GrpObj.differential j.hom.hom).toLinearMap.range ≤ positiveRaySpace S H eta →
            ∃ f : K ⟶ U, f ≫ i = j)) ∧
      (∀ (K : Grp (Over (Spec (.of F)))) (j : K ⟶ H),
        IsClosedSubgroupScheme j.hom.hom → Smooth K.X.hom → ConnectedSpace K.X.left →
        IsStable S H j →
        (GrpObj.differential j.hom.hom).toLinearMap.range = positiveRaySpace S H eta →
          ∃ e : K ≅ U, e.hom ≫ i = j) := by
  sorry

end AlgebraicGeometry.TorusCharacterTangent
