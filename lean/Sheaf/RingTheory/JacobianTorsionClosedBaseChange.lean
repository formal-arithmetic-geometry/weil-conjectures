/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.RingTheory.CompletedPolynomialConormal
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme

import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Finiteness.Ideal
import WeilConjectures.Algebra.ChangeIdealCompletion

/-!
# Closed base change preserves completed Jacobian torsion

Source: Stacks Project, restricted.tex, Tag 0GB2, Tag 0AJU condition (3),
remark-take-bar and equation-base-change-to-closed
(blueprint: lem-per-jacobian-torsion-closed-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

open AlgebraicGeometry

/-- The actual closed quotient `E/HE` for `E` the specified completed presentation.
Source: Stacks Project, restricted.tex, remark-take-bar
(blueprint: lem-per-jacobian-torsion-closed-base-change). -/
abbrev CompletedPolynomialClosedQuotient {A : Type u} [CommRing A]
    (I : Ideal A) (r : ℕ) (J : Ideal (rigPolynomialCompletion I r)) (H : Ideal A) :=
  (rigPolynomialCompletion I r ⧸ J) ⧸
    H.map (algebraMap A (rigPolynomialCompletion I r ⧸ J))

/-- Closed base change preserves the power-torsion kernel and cokernel of the continuous
conormal differential. Both annihilation conditions use ideal actions on submodules;
the cokernel is the quotient of the target by the range of the canonical differential.

Source: Stacks Project, restricted.tex, Tag 0GB2, Tag 0AJU condition (3),
remark-take-bar and Tags 0AJP--0AJQ
(blueprint: lem-per-jacobian-torsion-closed-base-change).

Proof:
1. Finite-type Noetherian permanence makes A[x] and A/H Noetherian. Completion is
   Noetherian by lem-weil-pbc-adic-completion-noetherian; its quotient E is Noetherian.
   The completion-mod-ideal theorem gives completeness of the polynomial completion.
2. Apply lem-weil-pbc-completion-finite-module-tensor over E to E/HE, and over A[x]
   to A[x]/HA[x]. The canonical comparisons identify their completions with E/HE
   and P/HP. Coefficient reduction identifies A[x]/HA[x] with (A/H)[x].
3. Equal vanishing loci give equal radicals by lem-weil-pbc-zero-locus-eq-iff-radical-eq.
   Finite generation and lem-weil-pbc-fg-ideal-radical-power supply positive u,v
   with (I(A/H))^u ≤ K and K^v ≤ I(A/H). By lem-weil-pbc-change-ideal-completion,
   E/HE is K-complete and P/HP is the K-completed polynomial ring. The image J0 of J
   gives its quotient presentation of E/HE, with s = r.
4. The induced q : J/J² → J0/J0² is surjective and kills H(J/J²). Partial derivatives
   preserve I-powers and commute coefficientwise with reduction and cofinal reindexing.
   The Leibniz rule makes the conormal arrows well-defined and δ0 q = ρ δ,
   where ρ is coordinate reduction. These identities hold in every finite quotient.
5. For a ∈ I^c, lift a times every standard basis vector through δ, using cokernel
   annihilation, to get α with δα = a id. Then αδ - a id lands in ker δ, which a kills.
   Thus h = aα satisfies δh = a² id and hδ = a² id, including the empty basis case.
6. E-linearity lets qh factor through ρ to h0. Surjectivity of q and ρ descends the
   identities to δ0 h0 = ā² id and h0 δ0 = ā² id. They kill the new kernel and cokernel;
   no preservation of kernels by a nonflat tensor product is asserted.
7. Choose t generators b_i of I^c. Each b_i² kills both new modules. Every product of
   t+1 generators repeats one, so (I^c)^(t+1) lies in (b_i²). Therefore I^(c(t+1))
   kills both. Since K^v ≤ I(A/H), d = vc(t+1) works. The formulas also handle
   t = 0 and c = 0, and give the claimed presentation and both annihilation clauses. -/
theorem jacobianTorsion_closedBaseChange {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (r : ℕ) (J : Ideal (rigPolynomialCompletion I r))
    [IsAdicComplete I (rigPolynomialCompletion I r ⧸ J)] (c : ℕ)
    (hker : I ^ c • (rigJacobianDifferential r I J).ker ≤ ⊥)
    (hcoker : I ^ c •
      (⊤ : Submodule A ((Fin r → (rigPolynomialCompletion I r ⧸ J)) ⧸
        (rigJacobianDifferential r I J).range)) ≤ ⊥)
    (H : Ideal A) (K : Ideal (A ⧸ H))
    (hV : PrimeSpectrum.zeroLocus ((I.map (Ideal.Quotient.mk H)) : Set (A ⧸ H)) =
      PrimeSpectrum.zeroLocus (K : Set (A ⧸ H))) :
    IsAdicComplete K (CompletedPolynomialClosedQuotient I r J H) ∧
    ∃ (s : ℕ) (J0 : Ideal (rigPolynomialCompletion K s)),
      Nonempty ((rigPolynomialCompletion K s ⧸ J0) ≃ₐ[A ⧸ H]
        CompletedPolynomialClosedQuotient I r J H) ∧
      ∃ d : ℕ,
        (K ^ d • (rigJacobianDifferential s K J0).ker ≤ ⊥) ∧
        (K ^ d •
          (⊤ : Submodule (A ⧸ H) ((Fin s → (rigPolynomialCompletion K s ⧸ J0)) ⧸
            (rigJacobianDifferential s K J0).range)) ≤ ⊥) := by
  sorry

end Algebra
