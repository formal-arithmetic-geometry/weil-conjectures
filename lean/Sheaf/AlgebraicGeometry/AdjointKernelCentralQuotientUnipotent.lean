/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.AdjointKernelPoints
public import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization

/-! # The adjoint kernel modulo the scheme-theoretic centre is unipotent

Source: Milne, Algebraic Groups (2017), Proposition 14.23, p.285, and
Theorem 14.5, p.281 (blueprint: lem-sfb-adjoint-kernel-central-quotient-unipotent).

The specified closed inclusion of N represents the kernel of differentiated
conjugation on all test algebras. A closed embedding of U into GL_n whose points
satisfy the unitriangular equations is equivalently a closed subgroup of U_n.
The final equality of kernel subfunctors is tested on all algebras, including
nonreduced ones, and therefore identifies the scheme-theoretic kernel.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- The adjoint kernel of a smooth connected affine algebraic group maps to a
closed unitriangular subgroup with scheme-theoretic kernel the centre.
The hypothesis hN specifies N as the actual adjoint kernel through its functor
of points, rather than an arbitrary representation with an unspecified action.
No smoothness, connectedness or reducedness of N or U is assumed.

Source: Milne, Algebraic Groups (2017), Proposition 14.23, p.285;
Theorem 14.5(a),(b), p.281; Theorem 5.39, p.108
(blueprint: lem-sfb-adjoint-kernel-central-quotient-unipotent).

Proof plan:
1. Apply lem-sfb-conjugation-finite-jet-kernel with r at least max(1,r0).
   Its representation on B/I^(r+1) has kernel Z(G). Central points act
   identically by conjugation and hence lie in N. Its restriction to N
   therefore has kernel Z(G), on every commutative test algebra.
2. By lem-sc-rational-tangent-cotangent-duality, the tangent space is the
   dual of I/I^2. Substitution in the dual-number formula
   f maps to e*(f) + epsilon lambda([f-e*(f)]) identifies conjugation on
   tangent vectors with dual pullback on the cotangent space. Over every
   test algebra A, hN makes all these tangent vectors fixed. A dual basis
   of the finite free A-module A tensor (I/I^2) makes its action identity.
3. Products of i elements of I/I^2 span I^i/I^(i+1): in a term b x1 ... xi,
   replace b by its residue modulo I. Multiplicativity then makes the
   action on each graded quotient identity, also after arbitrary base
   change. The degree-zero quotient is the trivial representation F.
4. Lift bases of the graded quotients and order deepest layers first.
   In this basis the restricted jet representation is upper triangular
   with every diagonal entry 1. The residue quotient ensures n is positive.
5. Apply lem-sfb-algebraic-group-homomorphism-factorization to this
   representation. Its closed image U in GL_n satisfies the unitriangular
   equations over every test algebra, hence is closed in U_n. The map
   q to this image has the same scheme-theoretic kernel Z(G). The kernel
   clause, tested on every A, gives precisely the final equivalence. -/
theorem adjointKernel_central_quotient_unipotent
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) (hG : SolvableGroupStructure.IsAlgebraic G)
    (hsm : Smooth G.X.hom) (hc : ConnectedSpace G.X.left)
    (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ G)
    (hiN : IsClosedSubgroupScheme iN.hom.hom)
    (hN : ∀ (A : Type u) [CommRing A] [Algebra F A],
      Set.range (fun x : StandardGroupSchemes.affine F A ⟶ N.X ↦ x ≫ iN.hom.hom) =
        adjointKernelPoints G A) :
    ∃ n : ℕ, 0 < n ∧ ∃ (U : Grp (Over (Spec (.of F))))
      (j : U.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) F) (q : N ⟶ U),
      IsClosedSubgroupScheme j ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : (Spec (.of A)).asOver (Spec (.of F)) ⟶ U.X),
        (∀ a : Fin n,
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) F A
            (x ≫ j)).val (ULift.up a) (ULift.up a) = 1) ∧
        ∀ a b : Fin n, b < a →
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) F A
            (x ≫ j)).val (ULift.up a) (ULift.up b) = 0) ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A],
        Set.range (fun x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker q.hom.hom ↦
          x ≫ GrpObj.kerι q.hom.hom ≫ iN.hom.hom) =
            ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A) ∧
      ∀ (A : Type u) [CommRing A] [Algebra F A]
        (g : StandardGroupSchemes.affine F A ⟶ N.X),
        g ≫ q.hom.hom = 1 ↔
          g ≫ iN.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A := by
  sorry

end AlgebraicGeometry
