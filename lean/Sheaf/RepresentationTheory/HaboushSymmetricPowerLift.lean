/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet

/-! # Haboush symmetric-power lifting

Source: Alper, Adequate moduli spaces, Theorem 9.7.5 and Lemma 9.2.5(5-prime).
(blueprint: lem-sfb-haboush-symmetric-power-lift).

The degree-N component is the Nth power of the range of the generator inclusion.
The induced coaction is the unique algebra map extending the given coaction on
those generators. Evaluation at lambda is Sym^N(lambda), followed by Sym^N(k) = k.
-/

set_option autoImplicit false

@[expose] public section

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.RationalRepresentation

/-- A surjection to the trivial representation has an invariant lift in positive symmetric degree.
Source: Alper, Theorem 9.7.5 and Lemma 9.2.5(5-prime), equivalently Lemma 9.2.8(1),(2),(6).
(blueprint: lem-sfb-haboush-symmetric-power-lift).

Proof plan, following the seven steps of the node:
1. Extend k to an algebraic closure K (def-weil-algebraic-closure). Dualize V_K to W;
   lambda_K is a nonzero fixed vector x. A basis identifies the symmetric powers
   after base change, compatibly with coactions and evaluation at lambda.
2. Pull the W-action back along the faithfully flat central cover T times S -> H_K
   (lem-sfb-reductive-torus-simply-connected-cover); its coordinate pullback is injective.
3. Expand the torus coaction in Laurent monomials. Coassociativity and the counit
   give the weight decomposition. Projection pi onto weight zero is S-equivariant,
   T-invariant, and fixes x, including when the torus has rank zero.
4. Apply lem-sfb-steinberg-endomorphism-detection to the weight-zero module and x.
   Obtain nonzero E and phi into End(E); its invariant endomorphisms are scalars.
   Normalize phi(x) to id_E and set n = dim(E) > 0.
5. The signed determinant polynomial of phi lies in Sym^n(U*), with value 1 at x
   (def-weil-pbc-matrix-determinant). The square case of lem-weil-pbc-cauchy-binet
   gives multiplicativity, so conjugation preserves it as a coordinate-algebra
   identity over K[S], without division by n!.
6. Pull back along pi to obtain a T times S invariant. Injectivity of the coordinate
   pullback, retained by tensoring over a field, makes it H_K invariant. The
   equivariant double-dual identification yields q_K in Sym^n(V_K) with evaluation 1.
7. Expand the finitely many coefficients of q_K in a k-independent family in K
   starting with 1. Comparing coefficients in the coaction and evaluation identities
   gives an invariant q over k with evaluation 1, in the same positive degree n.
The invariant identity is in the coordinate Hopf algebra, rather than only on k-points.
-/
theorem exists_invariant_symmetric_power_lift
    {k : Type u} [Field k] (H : Scheme.{u}) [H.Over (Spec (.of k))]
    [GrpObj (H.asOver (Spec (.of k)))] [IsAffine H]
    (hH : ReductiveTorusCentralizer.IsReductive (Grp.mk (H.asOver (Spec (.of k)))))
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : V →ₗ[k] V ⊗[k] Γ(H, ⊤))
    (hcoassoc : HopfAction.Coassociative k Γ(H, ⊤) V ρ)
    (hcounit : HopfAction.Counital k Γ(H, ⊤) V ρ) (ell : V →ₗ[k] k)
    (hell : Function.Surjective ell)
    (heq : ∀ v : V, ell.rTensor Γ(H, ⊤) (ρ v) = ell v ⊗ₜ[k] (1 : Γ(H, ⊤))) :
    ∃ (N : ℕ) (q : SymmetricAlgebra k V), 0 < N ∧
      q ∈ (SymmetricAlgebra.ι k V).range ^ N ∧
      SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι k V).rTensor Γ(H, ⊤) ∘ₗ ρ) q =
          q ⊗ₜ[k] (1 : Γ(H, ⊤)) ∧
      SymmetricAlgebra.lift ell q = 1 := by
  sorry

end AlgebraicGeometry.RationalRepresentation
