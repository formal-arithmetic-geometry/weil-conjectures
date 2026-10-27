/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q149
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Galois descent and scalar-extension detection for affine closed subgroups

Source: Milne, Algebraic Groups (2017), 1.54(a)-(b), A.64-A.66
(blueprint: lem-sfb-galois-descent-affine-subgroups).

The defining ideal is the kernel of the map on global sections. The existing
`baseChangeMap` and `specAlgEquivOver` give the canonical semilinear action;
on coordinate rings it sends `a ⊗ λ` to `a ⊗ σ(λ)`. Equality of subgroup schemes
is expressed by an isomorphism commuting with their embeddings, and inclusion
by a factorization of embeddings. These retain the full scheme structures.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

set_option autoImplicit false

/-- A Galois-stable closed subgroup of an affine group descends uniquely, including
for infinite Galois extensions.
Source: Milne 1.54(b), A.64-A.66
(blueprint: lem-sfb-galois-descent-affine-subgroups).

Proof: (1) Apply lem-sfb-galois-stable-subspace-descent to the defining ideal I
inside O(J) tensor L. Its contraction I₀ is an ideal, and the descended span is
exactly the extended ideal I₀ O(J_L), since multiplication by pure tensors preserves it.
(2) Form Spec(O(J)/I₀). The quotient tensor calculation from
lem-weil-pbc-algebra-tensor-pushout-universal-property identifies its base change
with V over J_L. The quotient is finitely generated, so the scheme is of finite type.
(3) For every k-algebra R, faithful flatness of R → R tensor L and
lem-weil-pbc-faithfully-flat-ideal-contraction reflect vanishing of each defining
equation. Identity, products and inverses therefore descend from V, giving the
closed subgroup structure (def-sc-group-scheme-subgroup).
(4) Faithfully flat contraction detects equality of defining ideals, proving
uniqueness as a subgroup scheme, i.e. an isomorphism over J. -/
theorem galois_descent_affine_subgroups
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (J : Over (Spec (.of k))) [GrpObj J] [IsAffine J.left]
    [LocallyOfFiniteType J.hom] [QuasiCompact J.hom]
    (V : Over (Spec (.of L))) [GrpObj V] [IsAffine V.left]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (j : V ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj J)
    [IsClosedSubgroupScheme j]
    (hstable : ∀ σ : L ≃ₐ[k] L,
      Ideal.comap (baseChangeMap J.hom (specAlgEquivOver σ)).appTop.hom
        (RingHom.ker j.left.appTop.hom) = RingHom.ker j.left.appTop.hom) :
    ∃ (N : Over (Spec (.of k))) (gN : GrpObj N) (i : N ⟶ J),
      @IsClosedSubgroupScheme k _ N J gN _ i ∧
      IsAffine N.left ∧ LocallyOfFiniteType N.hom ∧ QuasiCompact N.hom ∧
      (∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj N ≅ V,
        e.hom ≫ j = (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map i) ∧
      ∀ (N' : Over (Spec (.of k))) (gN' : GrpObj N') (i' : N' ⟶ J),
        @IsClosedSubgroupScheme k _ N' J gN' _ i' →
        (∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj N' ≅ V,
          e.hom ≫ j =
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map i') →
        ∃ e : N' ≅ N, e.hom ≫ i = i' := by
  sorry

/-- Inclusion of closed subgroup schemes is detected by any field extension.
Source: Milne 1.54(a), A.65 and faithfully flat ideal contraction
(blueprint: lem-sfb-galois-descent-affine-subgroups).

Proof: Write P,Q for the defining ideals. The tensor pushout universal property
identifies the defining ideals after base change with their extensions. Faithful
flatness and ideal contraction show that Q_K ≤ P_K iff Q ≤ P. A factorization of
closed embeddings is equivalent to this reversed ideal inclusion, by the quotient
universal property. This proves both directions. -/
theorem affine_closed_subgroup_inclusion_iff_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (J N M : Over (Spec (.of k))) [GrpObj J] [GrpObj N] [GrpObj M]
    [IsAffine J.left] [LocallyOfFiniteType J.hom] [QuasiCompact J.hom]
    (i : N ⟶ J) (j : M ⟶ J) [IsClosedSubgroupScheme i] [IsClosedSubgroupScheme j] :
    (∃ h : N ⟶ M, h ≫ j = i) ↔
      ∃ h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj N ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj M,
        h ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j =
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i := by
  sorry

/-- Equality as closed subgroup schemes is detected by any field extension.
Source: Milne 1.54(a), A.65
(blueprint: lem-sfb-galois-descent-affine-subgroups).

Proof: Apply faithfully flat ideal contraction to both inclusions of the defining
ideals. Equivalently apply the preceding inclusion assertion in both directions;
the two factorizations are inverse because the closed embeddings are monomorphisms. -/
theorem affine_closed_subgroup_eq_iff_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (J N M : Over (Spec (.of k))) [GrpObj J] [GrpObj N] [GrpObj M]
    [IsAffine J.left] [LocallyOfFiniteType J.hom] [QuasiCompact J.hom]
    (i : N ⟶ J) (j : M ⟶ J) [IsClosedSubgroupScheme i] [IsClosedSubgroupScheme j] :
    (∃ e : N ≅ M, e.hom ≫ j = i) ↔
      ∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj N ≅
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj M,
        e.hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j =
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i := by
  sorry

/-- Normality on all algebra points is detected by any field extension.
Source: Milne 1.51, 1.54(a), A.65-A.66 and faithful flatness
(blueprint: lem-sfb-galois-descent-affine-subgroups).

Proof: A K-algebra is a k-algebra; the tensor universal property identifies the
points of N_K and J_K on it with those of N and J. Thus normality implies normality
after extension. Conversely, for any k-algebra R, extend g in J(R), n in N(R) to
R tensor K. Normality there puts gng⁻¹ in N_K. Every defining equation then
vanishes after R → R tensor K, which is injective by faithful flatness and ideal
contraction with the zero ideal. The equations already vanish in R, proving
normality on every k-algebra, including nonreduced algebras. -/
theorem affine_closed_subgroup_normal_iff_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (J N : Over (Spec (.of k))) [GrpObj J] [GrpObj N]
    [IsAffine J.left] [LocallyOfFiniteType J.hom] [QuasiCompact J.hom]
    (i : N ⟶ J) [IsClosedSubgroupScheme i] :
    IsNormalSubgroupScheme i ↔
      IsNormalSubgroupScheme
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) := by
  sorry

end AlgebraicGeometry
