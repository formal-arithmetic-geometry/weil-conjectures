/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard

/-!
# Second Kummer cohomology of a curve

Source: blueprint sec-curve-estimates, sk-prop-h2, lem-sc-second-kummer-divisors;
Stacks Project, Tags 03PK and 03RQ, the long exact Kummer sequence
(blueprint: lem-sc-second-kummer-divisors).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- Source: blueprint lem-sc-second-kummer-divisors; Stacks Project, Tags 03PK and 03RQ.
For any curve over an algebraically closed field and any positive invertible integer n,
second Kummer cohomology is Pic/n via the Kummer coboundary, and H² of Gₘ vanishes.

Proof step 1: `lem-sc-brauer-zero-all-curves` gives vanishing of H²(Gₘ). Invertibility
of n in the field implies invertibility on C. By `lem-sc-kummer-exact`, the sequence
of `def-sc-kummer-sequence` is short exact.
Proof step 2: apply clause 2 of `lem-weil-pbc-pullback-cohomology-long-exact-ladder`
with the identity of C. The degree-one and degree-two terms give the Kummer boundary
from H¹(Gₘ) onto H²(μₙ), with kernel n H¹(Gₘ), since H²(Gₘ) vanishes.
Under the canonical group isomorphism of `lem-sc-h1-gm-pic`, the power map is
multiplication by n on Pic. The boundary therefore descends to an isomorphism
Pic/n → H²(μₙ); invert it for the displayed orientation. The equality below records
this identification on every Picard class, for every proof of invertibility on C.
(blueprint: lem-sc-second-kummer-divisors) -/
theorem exists_addEquiv_secondKummer_divisors {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] (n : ℕ) (hn : (n : k) ≠ 0) :
    (∃ e : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+
        Additive C.Pic ⧸ (zsmulAddGroupHom (α := Additive C.Pic) (n : ℤ)).range,
      ∀ (hnC : IsUnit (n : Γ(C, ⊤))) (L : Additive C.Pic),
        e (C.kummerδ₁ n hnC (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L)) =
          QuotientAddGroup.mk L) ∧
      Subsingleton C.CohomologicalBrauerGroup := by
  sorry

end AlgebraicGeometry.IsCurve
