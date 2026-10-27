/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # The multiplicative part of a commutative affine algebraic group

Source: Milne, Algebraic Groups (2017), Theorem 16.13(a), p.328, Note 16.17, p.329,
and Theorem 14.5 and Corollary 14.9, pp.281--282
(blueprint: lem-sfb-commutative-multiplicative-part).

Unipotence is expressed by a closed faithful matrix representation whose values
are upper unitriangular over every test algebra, including nonreduced algebras.
Scalar-extension compatibility says that the pulled-back inclusion is again
the largest multiplicative-type subgroup of the pulled-back ambient group.
This identifies the actual closed subgroups, independently of their presentations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A commutative affine group of finite type has a largest multiplicative-type
closed subgroup with represented unipotent fppf quotient, and this subgroup
commutes with every field extension. No smoothness or perfectness is required.

Source: Milne, Algebraic Groups (2017), Theorem 16.13(a), p.328,
Note 16.17, p.329, and Theorem 14.5, pp.281--282
(blueprint: lem-sfb-commutative-multiplicative-part).

Proof plan, following the seven steps of the DAG node:
1. The coordinate algebra B of C is Noetherian by lem-pc-affine-finite-type-algebra
   and lem-weil-pbc-finite-type-algebra-noetherian. Intersect all closed subgroups
   with unipotent quotient. These quotients exist by lem-sfb-affine-normal-quotient-geometry.
   Their ideal sum is finitely generated, so finitely many subgroups have the same
   scheme-theoretic intersection S (def-weil-pbc-noetherian-ring and the affine
   fibre-product formula lem-weil-pbc-fibre-product-affine-spectra).
2. The map to the product of those quotients has kernel S. Apply
   lem-sfb-algebraic-group-homomorphism-factorization and
   lem-sfb-faithfully-flat-group-quotient-universal to embed C/S in that product.
   Block diagonal matrices embed the product in a unitriangular group. The empty
   product embeds in U_1. Thus C/S is unipotent, and S is minimal with this property.
3. For a homomorphism S -> Ga let N be its kernel. Its quotient S/N is closed in
   Ga = U_2. Subgroup correspondence gives an extension S/N -> C/N -> C/S.
   By lem-sfb-unitriangular-extension it is unipotent. Minimality forces N = S,
   so every such additive homomorphism vanishes.
4. By lem-sfb-affine-group-coordinate-hopf, additive homomorphisms are primitive
   coordinate elements. In L tensor k[S], express a primitive element with linearly
   independent L-coefficients over k. Applying coordinate functionals shows every
   B-coefficient is primitive and hence zero. Thus the vanishing persists under
   every field extension (def-weil-pbc-module-tensor-product).
5. Over the algebraic closure, lem-sfb-multiplicative-additive-vanishing-criterion
   makes S diagonalizable. Generators of its finitely generated character group
   give a surjection from a Laurent polynomial algebra, hence a closed immersion
   into a finite split torus. This is MultiplicativeType.IsMultiplicativeType S.
6. For any multiplicative-type H in C, lem-sfb-split-torus-subgroups-diagonalizable
   and lem-sfb-diagonalizable-to-unipotent-trivial make H -> C/S zero after
   algebraic closure. Tensoring a vector space with a field is injective, so this
   descends to k. The scheme-theoretic kernel is S, giving the required factorization.
7. For K/k, step 4 and step 5 make S_K multiplicative. The quotient base-change
   theorem identifies C_K/S_K with (C/S)_K. Tensoring the coordinate surjection
   of the unitriangular embedding preserves surjectivity, so this quotient is
   unipotent. Apply the vanishing and descent argument of step 6 over K: every
   multiplicative-type subgroup of C_K factors through S_K. This is equality
   with the largest closed subgroup (C_K)_s, not just equality on field points. -/
theorem commutative_multiplicative_part
    {k : Type u} [Field k] (C : Grp (Over (Spec (.of k))))
    [IsAffine C.X.left] [LocallyOfFiniteType C.X.hom] [QuasiCompact C.X.hom]
    [IsCommMonObj C.X] :
    ∃ (S Q : Grp (Over (Spec (.of k)))) (i : S ⟶ C) (q : C ⟶ Q),
      SolvableGroupStructure.IsAlgebraic S ∧ SolvableGroupStructure.IsAlgebraic Q ∧
      IsClosedSubgroupScheme i.hom.hom ∧ MultiplicativeType.IsMultiplicativeType S ∧
      (∀ (H : Grp (Over (Spec (.of k)))) (j : H ⟶ C),
        IsClosedSubgroupScheme j.hom.hom → MultiplicativeType.IsMultiplicativeType H →
          ∃ f : H ⟶ S, f ≫ i = j) ∧
      SolvableGroupStructure.IsFppfQuotient i.hom.hom q ∧
      (∃ n : ℕ, 0 < n ∧
        ∃ r : Q.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
          IsClosedSubgroupScheme r ∧
          ∀ (A : Type u) [CommRing A] [Algebra k A]
            (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ Q.X),
            (∀ a : Fin n,
              (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val
                ⟨a⟩ ⟨a⟩ = 1) ∧
            (∀ a b : Fin n, b < a →
              (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val
                ⟨a⟩ ⟨b⟩ = 0)) ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsClosedSubgroupScheme ((MultiplicativeType.baseChange (K := K)).map i).hom.hom ∧
        MultiplicativeType.IsMultiplicativeType
          ((MultiplicativeType.baseChange (K := K)).obj S) ∧
        ∀ (H : Grp (Over (Spec (.of K))))
          (j : H ⟶ (MultiplicativeType.baseChange (K := K)).obj C),
          IsClosedSubgroupScheme j.hom.hom → MultiplicativeType.IsMultiplicativeType H →
            ∃ f : H ⟶ (MultiplicativeType.baseChange (K := K)).obj S,
              f ≫ (MultiplicativeType.baseChange (K := K)).map i = j := by
  sorry

end AlgebraicGeometry
