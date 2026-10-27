/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Multiplicative-to-unipotent vanishing over arbitrary base algebras

Source: Milne, Algebraic Groups (2017), Proposition 15.18, printed p.312,
and Theorem 14.5, printed pp.281--282
(blueprint: lem-sfb-multiplicative-unipotent-base-algebra-vanishing).

Unipotence is stated by a closed faithful representation whose matrix entries satisfy
unitriangular equations on every algebra. This includes nonsmooth group schemes.
Scalar extension is the finite-product-preserving pullback functor on group objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every homomorphism from a multiplicative-type group to a unipotent group is trivial
following extension to any base algebra, including a nonreduced or zero algebra.

Source: Milne, Algebraic Groups (2017), Proposition 15.18, printed p.312;
Theorem 14.5, pp.281--282, for the unitriangular characterization
(blueprint: lem-sfb-multiplicative-unipotent-base-algebra-vanishing).

Proof plan:
1. Put K = AlgebraicClosure k and S = R tensor_k K. The extension R -> S is faithfully
   flat by lem-weil-pbc-field-extension-base-change-faithfully-flat. Affine base change
   is tensor extension by lem-weil-pbc-fibre-product-affine-spectra. The coordinate map
   B -> B tensor_R S is injective by lem-weil-pbc-faithfully-flat-universally-injective.
   Thus equality of two maps out of D_R descends from S, using def-weil-affine-spectrum.
   The zero ring is included, since all its coordinate algebras are zero.
2. By lem-sfb-split-torus-subgroups-diagonalizable, the closed subgroup D_K of a split
   torus is D_K(M) for a finitely generated abelian group M. Tensor extension gives
   S[M]: s tensor (sum a_m e_m) maps to sum (s a_m)e_m, with inverse
   sum s_m e_m maps to sum s_m tensor e_m. These inverse ring maps preserve the
   coproduct e_m -> e_m tensor e_m of def-sfb-ring-diagonalizable-group.
3. A primitive element z = sum a_m e_m of S[M] is zero: compare the (m,m) coefficient
   in Delta z = z tensor 1 + 1 tensor z. For m nonzero this gives a_m = 0; at zero
   it gives a_0 = 2 a_0, hence a_0 = 0. The coefficient projections are S-linear,
   so no domain assumption is used. The coordinate image of the additive coordinate
   under any homomorphism D_S(M) -> Ga_S is primitive, by def-sc-gm-ga and the affine
   tensor-product identification. Therefore every such additive homomorphism is zero.
4. Compose f_S with the given closed faithful unitriangular representation. By
   lem-sfb-unitriangular-coordinate-filtration, successively kill the n(n-1)/2
   upper coordinates, ordered by increasing j-i and then i. Each coordinate is an
   additive homomorphism on the preceding kernel and hence zero by step 3. Kernels
   commute with base change by the fibre-product property in def-pc-fibre-product
   and def-pc-base-change. Their universal property gives group-homomorphism
   factorizations at each step, since the kernel inclusions are injective on points.
   The final kernel is trivial; for n = 1 the representation is already trivial.
5. Cancel the closed subgroup inclusion on all S-algebra points using
   def-sc-group-scheme-subgroup, then descend the resulting equality by step 1.
   Evaluating the equality at every R-algebra point gives the displayed formula.
   Reducedness, smoothness and connectedness are never used.

The unitriangular equations on every algebra mean precisely factorization through
U_n: its defining equations generate a polynomial ideal, and the universal affine
point tests that their pullbacks vanish. The faithful representation is closed in
GL_n, so its factorization through the closed subscheme U_n is also closed. -/
theorem multiplicative_unipotent_base_algebra_vanishing
    {k : Type u} [Field k] (D U : Grp (Over (Spec (.of k))))
    [IsAffine D.X.left] [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom] [QuasiCompact U.X.hom]
    (hD : MultiplicativeType.IsMultiplicativeType D)
    (hU : ∃ (n : ℕ), 1 ≤ n ∧
      ∃ r : U.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
        IsClosedSubgroupScheme r ∧
        ∀ (B : Type u) [CommRing B] [Algebra k B]
          (x : (Spec (.of B)).asOver (Spec (.of k)) ⟶ U.X),
          (∀ i j : ULift.{u} (Fin n), j.down < i.down →
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k B (x ≫ r)).val i j = 0) ∧
          (∀ i : ULift.{u} (Fin n),
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k B (x ≫ r)).val i i = 1))
    (R : Type u) [CommRing R] [Algebra k R]
    (f : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp).obj D ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp).obj U) :
    f.hom.hom = 1 ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A]
        (d : (Spec (.of A)).asOver (Spec (.of R)) ⟶
          (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp).obj D).X),
        d ≫ f.hom.hom = 1 := by
  sorry

end AlgebraicGeometry
