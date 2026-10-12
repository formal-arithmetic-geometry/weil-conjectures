/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Dense-open comparison for prime-torsion module sheaves -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- The eight assertions are unchanged by extending the restriction from a dense open by zero.
Source: Stacks Project, Lemma 0GJA and its proof, specialized to prime-torsion coefficients
(blueprint: lem-pbc-q1-dense-open-prime-assertions).

Proof: Give the closed complement Z its reduced scheme structure. It is a finite union of
k-rational points, since X has dimension at most one and U contains all generic points.
The open-closed sequence is 0 → j_! j^* F → F → i_* i^* F → 0. Finite direct image is exact,
so H^q(X,i_* i^* F) equals H^q(Z,i^* F): zero for q > 0, and in degree zero the finite
product of the geometric stalks at Z. Those stalks are finite: constructibility gives
finitely generated modules and the coefficient ring is finite. This product is unchanged
by extension of algebraically closed fields. The long exact sequence therefore gives
isomorphisms H^q(X,j_! j^* F) → H^q(X,F) for q ≥ 2 and the exact five-term sequence in
degrees zero and one. The same statements hold on every open W of X, with dense open W ∩ U,
and after every algebraically closed field extension, compatibly with all maps and boundaries.
Assertions C1-C3 use the isomorphisms in degree at least two. C4-C5 use these isomorphisms
and the finite boundary product in the five-term sequence. For C6-C7, use the commuting
five-term ladders in degrees zero and one and the higher-degree isomorphisms. C8 follows
from the commuting restriction square in degree two. Both sheaves are constructible and
killed by r. If r differs from the characteristic, both have invertible torsion; if r equals
it, both are primary. Any exceptional invertible or different-primary condition forces
the corresponding prime-torsion sheaf to be zero and is automatic. Thus these arguments
apply to the conditional forms of all eight assertions, in both directions. The empty
scheme and U = X give respectively zero groups and the identity comparison. -/
theorem assertions_iff_dense_open_prime (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0)
    (U : X.Opens) (hU : Dense (U : Set X)) :
    IsCurve.Assertions Λ f F ↔ IsCurve.Assertions Λ f
      ((U.ι)_!open[ModuleCat.{u + 1} Λ].obj ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)) := by sorry

end AlgebraicGeometry.IsCurve
