/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Integral saturated sections of an fs log structure

Source: ILO, Exposé VI 1.1, printed p.69, and VIII 3.1.17, printed p.101;
the section theorem is the DAG's deduction from these chart and saturation conventions
(blueprint: lem-per-fs-log-sections-saturated).

The section monoids and their group completions are written multiplicatively, so `g ^ n`
renders the additive expression `n g`. No finite generation of sections is asserted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open Opposite

namespace AlgebraicGeometry

/-- Sections on every small étale object of a locally Noetherian fs log scheme are
integral and saturated in their canonical group completion.

Source: ILO VI 1.1, p.69 (fs charts), and VIII 3.1.17, p.101 (root saturation).
The assertion for sections is the following deduction, rather than a separately
stated theorem in that source.

Proof:
1. At a geometric point choose an fs chart P. With A the strict-local ring, G = Aˣ,
   E the inverse image of Aˣ in P, and f : E → G the structural homomorphism, the
   chart identifies the log stalk L with P ⊕_E G. The integral mixed-unit-pushout
   lemma [lem-sfb-integral-monoid-unit-pushout] makes L integral, even when f is not
   injective and G or P^gp has torsion.
2. Write all groups additively for this calculation. The universal properties of
   the pushout and group completion identify L^gp with
   K = (P^gp ⊕ G)/{(e,-f^gp(e)) : e ∈ E^gp}.
   If n[(v,u)] = [(p,w)] with n > 0 and p ∈ P, the quotient relation gives
   nv-p = e₁-e₂ with e₁,e₂ ∈ E. Hence
   n(v+e₂) = p+e₁+(n-1)e₂ ∈ P. Saturation of P implies v+e₂ ∈ P;
   [(v,u)] = [(v+e₂,u-f(e₂))] therefore lies in L. All stalks are saturated.
3. By the finite-equalities and restriction-stalk clauses of
   [lem-trf-finite-monoid-stalk-data-spreading], equality of section germs holds
   on pointed étale refinements covering the test object. Sheaf separation
   [def-weil-pbc-etale-sheaf-of-sets] detects equality globally. Thus sections embed
   into the product of the stalk group completions. Factoring through their own
   group completion proves the required injectivity and cancellation on every object.
4. Write g = j(a)-j(b) and suppose ng = j(c). Stalk saturation gives germs t with
   t+b=a, using stalk integrality. The representatives and finite-equalities clauses
   of [lem-trf-finite-monoid-stalk-data-spreading] spread these germs and equations
   to an étale cover, without requiring a finite subcover.
5. On each overlap, tᵢ+b=a=tⱼ+b. Section cancellation gives tᵢ=tⱼ. Sheaf gluing
   [def-weil-pbc-etale-sheaf-of-sets] gives t globally with t+b=a, so j(t)=g.
6. The identity étale object is allowed. On the empty object the empty-cover axiom
   makes the section monoid a singleton and its group completion trivial. The proof
   never assumes finite generation of sections or torsion freeness of their group.
(blueprint: lem-per-fs-log-sections-saturated). -/
theorem FineSaturatedLogScheme.sections_integral_saturated
    (X : FineSaturatedLogScheme.{u}) (U : X.scheme.Etale) :
    Function.Injective
      (Algebra.GrothendieckGroup.of (M := X.logStructure.monoidSheaf.obj.obj (op U))) ∧
    ∀ (g : Algebra.GrothendieckGroup (X.logStructure.monoidSheaf.obj.obj (op U)))
      (n : ℕ), 0 < n →
      (∃ m : X.logStructure.monoidSheaf.obj.obj (op U),
        Algebra.GrothendieckGroup.of m = g ^ n) →
      ∃ m : X.logStructure.monoidSheaf.obj.obj (op U),
        Algebra.GrothendieckGroup.of m = g := by
  sorry

end AlgebraicGeometry
