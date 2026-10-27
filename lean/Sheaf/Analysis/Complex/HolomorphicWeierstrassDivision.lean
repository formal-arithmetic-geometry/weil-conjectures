/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Topology.Germ

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Analytic Weierstrass division after linear regularization

Source: Frenkel, Séminaire H. Cartan 1951--52, exp. 10, Proposition 4, printed p. 5,
Theorem 1, pp. 2--3, and Theorem 1 bis, pp. 7--9.
(blueprint: lem-sfb-holomorphic-weierstrass-division)

`IsAnalyticAtZeroGerm` selects the holomorphic germs inside Mathlib's ring of all
function germs. Equality and arithmetic are those of this ambient ring, hence use
agreement on a neighbourhood and pointwise operations. The analytic operations
lemma ensures that these are the operations of the holomorphic germ algebra.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open Filter
open scoped Topology BigOperators

namespace Complex

/-- A germ at zero is holomorphic if it has a representative given near zero by a
convergent complex power series. A representative can be extended arbitrarily off
its neighbourhood; the extension does not affect the germ. For `E = Fin d → ℂ`
this predicate specifies the elements of `G_d`, including `d = 0`.

Source: Frenkel, Cartan seminar 1951--52, exp. 10, section 4, pp. 6--7.
(blueprint: lem-sfb-holomorphic-weierstrass-division). -/
def IsAnalyticAtZeroGerm {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Germ (𝓝 (0 : E)) ℂ) : Prop :=
  ∃ F : E → ℂ, AnalyticAt ℂ F 0 ∧ Germ.ofFun F = f

/-- Pull a function germ at zero back along a continuous complex-linear map.
This is composition on representatives, using the existing `Germ.compTendsto`.
It includes the coordinate change, last-axis restriction, and transverse projection
in analytic Weierstrass division.

Source: Frenkel, Cartan seminar 1951--52, exp. 10, Proposition 4 and Theorem 1 bis.
(blueprint: lem-sfb-holomorphic-weierstrass-division). -/
def linearPullbackAtZeroGerm {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (f : Germ (𝓝 (0 : F)) ℂ) : Germ (𝓝 (0 : E)) ℂ :=
  f.compTendsto L (L.continuous.tendsto' 0 0 L.map_zero)

/-- Every nonzero holomorphic germ in positive dimension can be made regular in
its last coordinate by an invertible complex-linear change. Division then has a
unique holomorphic quotient and a unique family of holomorphic transverse coefficients.
The dimension is `n + 1`; the family has type `Fin k`, so order zero has empty remainder.
A continuous linear equivalence is exactly an invertible linear map here, since all
spaces involved are finite dimensional. `Germ.value` evaluates the one-variable unit
at zero. In transverse dimension zero every function germ is a complex constant.

Source: Frenkel, Cartan seminar 1951--52, exp. 10, Proposition 4, p. 5,
Theorem 1, pp. 2--3, and Theorem 1 bis, pp. 7--9.
(blueprint: lem-sfb-holomorphic-weierstrass-division).

Proof plan (the node's six steps):
1. Use lem-sfb-weighted-taylor-banach-model to take the first nonzero homogeneous
   Taylor part H_k. By lem-sfb-mvpolynomial-infinite-evaluation choose v with H_k(v) nonzero.
   Choose v nonzero, using a coordinate vector if k=0. Complete v to the last column
   of an invertible matrix L. Substitution yields h(0,w)=w^k u(w), with u(0) nonzero.
   The analytic operations lemma makes h and u holomorphic.
2. For k=0, h is a unit and the quotient is g/h with no remainder. For positive k,
   normalize by u(w): B=h/u=w^k+c with c(0,w)=0. Division by B gives division by h
   after replacing the quotient Q by Q/u. Use lem-sfb-complex-analytic-function-operations.
3. In the weighted Taylor Banach model choose common radii for g and c. Shrink the
   transverse radii by a factor lambda so that the norm of c is less than t^k.
   Every monomial of c has positive transverse degree. If n=0, c=0 instead.
4. Let S_k delete the first k last-variable coefficients and shift the others down,
   and let R_k retain just those first k coefficients. Direct coefficient estimates
   give norm(S_k) at most t^(-k) and F=w^k S_k F+R_k F. Thus T=S_k composed with
   multiplication by c has norm less than one. Use the weighted Taylor Banach model.
5. By lem-sfb-banach-small-operator-invertible, I+T is invertible. Set
   Q=(I+T)^(-1)(S_k g) and R=g-BQ. Then S_k R=0, so R is a polynomial of degree
   less than k in w. Each coefficient slice has finite weighted transverse norm,
   hence is a holomorphic germ by the Taylor model. Return q=Q/u.
6. For a competing quotient and coefficient family, choose common smaller radii
   for all the finitely many germs and repeat the transverse shrinking. Injectivity
   of the Taylor germ map makes the equations coefficient identities. Subtracting
   and applying S_k gives (I+T)(Q-Q')=0. Small-operator invertibility forces Q=Q',
   hence q=q'; equality of the remaining coefficients forces every a_j=a'_j.
   This proves uniqueness among all holomorphic germs, without a fixed convergence disc. -/
theorem exists_holomorphic_weierstrass_division
    (n : ℕ) (f : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
    (hf : IsAnalyticAtZeroGerm f) (hfn : f ≠ 0) :
    ∃ (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ)) (k : ℕ)
      (u : Germ (𝓝 (0 : ℂ)) ℂ),
      IsAnalyticAtZeroGerm u ∧ u.value ≠ 0 ∧
      linearPullbackAtZeroGerm
          (ContinuousLinearMap.pi fun i : Fin (n + 1) ↦
            if i = Fin.last n then ContinuousLinearMap.id ℂ ℂ else 0)
          (linearPullbackAtZeroGerm L.toContinuousLinearMap f) =
        Germ.ofFun (fun w : ℂ ↦ w) ^ k * u ∧
      ∀ g : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ, IsAnalyticAtZeroGerm g →
        ∃! qa : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ ×
            (Fin k → Germ (𝓝 (0 : Fin n → ℂ)) ℂ),
          IsAnalyticAtZeroGerm qa.1 ∧ (∀ j : Fin k, IsAnalyticAtZeroGerm (qa.2 j)) ∧
          g = qa.1 * linearPullbackAtZeroGerm L.toContinuousLinearMap f +
            ∑ j : Fin k,
              linearPullbackAtZeroGerm
                  (ContinuousLinearMap.pi fun i : Fin n ↦
                    ContinuousLinearMap.proj (R := ℂ) i.castSucc) (qa.2 j) *
                Germ.ofFun (fun x : Fin (n + 1) → ℂ ↦ x (Fin.last n)) ^ (j : ℕ) := by
  sorry

end Complex
