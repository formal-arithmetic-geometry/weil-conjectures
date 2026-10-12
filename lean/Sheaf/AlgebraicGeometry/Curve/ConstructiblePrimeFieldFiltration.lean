/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.Curve.PrimeFieldFiltration

/-! # Constructible sheaves over finite rings have finite prime-field filtrations

Source: Stacks Project, Theorem 03SC, second proof paragraph; Lemma 03RZ.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Every constructible sheaf over a finite ring lies in the finite extension
closure of constructible sheaves with prime-field underlying abelian sheaves.
Source: Stacks Project, Theorem 03SC, second proof paragraph; Lemma 03RZ.
(blueprint: lem-v2-constructible-prime-field-filtration)

Proof: Let N be the positive additive order of 1 in the finite ring. Scalar
multiplication by N is zero on every module and hence on F. Factor N into prime
powers and use integer Chinese remainder idempotents to split F into its finitely
many primary summands. Each summand is a kernel of an endomorphism of F, and is
constructible by 03RZ. For a summand killed by r^e, induct on e. If e = 1, its
sections have their canonical ZMod r action, lifted to ULift(ZMod r); restriction
maps are linear, and the sheaf condition is unchanged. On a constructible
stratification, finite locally constant Lambda-module values become finite locally
constant prime-field values, so the new sheaf G is constructible with the same
underlying abelian sheaf. This gives the prime constructor. If e > 1, take the
kernel K of multiplication by r and its cokernel Q in F. The sequence
0 -> K -> F -> Q -> 0 is short exact; K is killed by r and Q by r^(e-1).
Both are constructible by 03RZ; apply the base case to K and induction to Q,
then the extension constructor. Reassemble primary summands by the split short
exact sequences for their finite direct sum. For N = 1 the sheaf is zero: use
the zero prime-field sheaf for r = 2 and the unique isomorphism of underlying
zero sheaves. Thus the zero ring, zero sheaf and empty scheme are also covered.
This argument uses only finite coefficients and constructibility, with no curve
or cohomology hypotheses. -/
theorem constructible_hasPrimeFieldFiltration
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    HasPrimeFieldFiltration Λ X F := by sorry

end AlgebraicGeometry.Scheme
