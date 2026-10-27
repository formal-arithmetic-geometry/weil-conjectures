module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Finiteness

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.FiniteType

/-! # Diagonalizability detected by additive homomorphisms

Source: Milne, Algebraic Groups (2017), Theorem 12.18(a),(b),(d), pp.237--238,
and Theorems 12.8--12.9(a), pp.233--234
(blueprint: lem-sfb-multiplicative-additive-vanishing-criterion).

The zero homomorphism is the composite through the base and the identity section of G_a.
The diagonalizable presentation uses the canonical Hopf structure on the group algebra.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- An affine finite-type group over an algebraically closed field is diagonalizable
if and only if it is commutative and every homomorphism to the additive group is zero.
No smoothness, reducedness or connectedness is required.

Source: Milne, Algebraic Groups (2017), Theorem 12.18(a),(b),(d), pp.237--238,
and Theorems 12.8--12.9(a), pp.233--234
(blueprint: lem-sfb-multiplicative-additive-vanishing-criterion).

Proof plan:
1. By lem-sfb-affine-group-coordinate-hopf and lem-sfb-hopf-spectrum-functor,
   pullback of the additive coordinate identifies group homomorphisms G → G_a with
   primitive elements p of H = F[G], satisfying Δp = p ⊗ 1 + 1 ⊗ p. Applying the
   counit twice gives εp = 2εp, hence εp = 0, and the antipode identity gives S(p) = -p.
   Thus polynomial substitution at p preserves all Hopf operations; the two
   constructions are inverse by the affine-spectrum correspondence. Zero maps match p = 0.
2. For H = F[M], swapping the tensor factors fixes Δ, so D_F(M) is commutative.
   Comparing coefficients of e_m ⊗ e_m in a primitive element gives c_m = 0 for
   m ≠ 0 and c_0 = 2c_0, hence c_0 = 0 in every characteristic. Tensor products of
   basis-coordinate maps justify the comparison, giving the forward Hom vanishing.
3. Conversely, assume commutativity and Hom vanishing. By
   lem-sfb-comodule-finite-subrepresentation, each h ∈ H lies in a finite stable
   subspace W of the regular comodule. Choose a finite basis w_j using
   lem-weil-pbc-vector-space-free. Write Δw_j = Σ_i w_i ⊗ c_ij. Coassociativity
   gives Δc_ij = Σ_l c_il ⊗ c_lj, and the counit gives εc_ij = δ_ij.
   The span C of these finitely many coefficients is a finite-dimensional coalgebra;
   w_j = Σ_i ε(w_i)c_ij shows W ⊆ C and h ∈ C.
4. The finite dual A = Cᵛ has convolution multiplication and unit ε|C. The Hopf
   identities give associativity and a unit; commutativity of G makes A commutative.
   Apply lem-sfb-finite-algebra-split-or-dual-quotient. A surjection A → F[ε] writes
   as x ↦ x(a) + x(b)ε by finite duality, with b ≠ 0. Multiplicativity and unitality
   give Δa = a ⊗ a, Δb = a ⊗ b + b ⊗ a, εa = 1 and εb = 0.
5. The antipode gives S(a)a = 1 in H. Multiplicativity of Δ shows that S(a) has
   coproduct S(a) ⊗ S(a), so bS(a) is a nonzero primitive element. This contradicts
   step 1 and Hom vanishing. Consequently the other alternative holds: Cᵛ ≅ F^n.
6. The coordinate forms of this product are evaluations at a basis a_i of C.
   Their multiplicativity and units give Δa_i = a_i ⊗ a_i and εa_i = 1.
   The zero coalgebra corresponds to n = 0. Hence every C, and by step 3 all H,
   is spanned by group-like elements.
7. By lem-sfb-coalgebra-group-like-independent the group-like elements form a basis.
   They form an abelian group M under multiplication, with inverse the antipode.
   The basis map F[M] → H is therefore a Hopf-algebra isomorphism.
8. By lem-weil-pbc-lft-affine-pairs, H is a finitely generated F-algebra. The union
   of the finite supports of algebra generators in the group-like basis generates a
   subgroup N of M whose span is H. Independence forces N = M, so M is finitely
   generated. Apply lem-sfb-hopf-spectrum-functor to the Hopf isomorphism and its
   inverse to obtain the group-scheme isomorphism G ≅ D_F(M). -/
theorem diagonalizable_iff_commutative_and_additive_hom_zero
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Over (Spec (.of F))) [GrpObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    (∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (Grp.mk G ≅ diagonalizableGroup F M)) ↔
    IsCommMonObj G ∧
      ∀ (f : G ⟶ StandardGroupSchemes.additive F), IsMonHom f →
        f = toUnit G ≫ MonObj.one (X := StandardGroupSchemes.additive F) := by
  sorry

end AlgebraicGeometry
