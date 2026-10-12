/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

/-!
# The curve assertions for finite sums with a common prime annihilator

Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C
(blueprint: lem-pbc-t2-prime-biproduct-assertions).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.IsCurve

/-- The eight conditional assertions are componentwise for a finite biproduct of
constructible sheaves killed by one fixed prime. The ambient sheaf may be any object
isomorphic to the biproduct; there is no open immersion in this statement.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C
(blueprint: lem-pbc-t2-prime-biproduct-assertions).

Proof: Forgetting the module structure, inverse image, and cohomology are additive;
they preserve finite biproducts and isomorphisms. Naturality in the coefficient
sheaf identifies every field-extension and open-restriction comparison with the
finite sum of its component comparisons. Zero and finite cohomology groups are
equivalent to zero and finite component groups, respectively. A finite sum of
maps is bijective, respectively surjective, exactly when each component map is.
This proves C1, C2, C5, C7 and C8 in both directions, since the affine and proper
hypotheses depend only on the fixed morphism f. All summands, and their finite
sum, are constructible. For C3, let p be the positive characteristic. If p = r,
all stalks are p-primary and the vanishing condition is componentwise. If p ≠ r,
a stalk killed by r that is also p-primary is zero, by Bezout for r and p^m;
thus any summand satisfying the C3 hypothesis is zero. Likewise, if the whole
sum satisfies it then the whole sum is zero. These exceptional assertions are
automatic. For C4 and C6, if r is invertible in k (including characteristic zero),
all the sheaves have invertible-order torsion. If char k = r, any of these
sheaves with invertible-order torsion is zero: each stalk element is killed both
by r and by an integer coprime to r. Again the exceptional assertions are
automatic. Transport along the given isomorphism preserves constructibility,
torsion hypotheses and all comparison maps. When the index is empty the
biproduct is zero and all eight assertions hold, agreeing with the vacuous
right side. -/
theorem assertions_iff_of_prime_biproduct_iso (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (r : ℕ) [Fact r.Prime] {ι : Type} [Finite ι]
    (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hGc : ∀ a, Scheme.IsConstructibleSheaf (G a)) (hGr : ∀ a, r • 𝟙 (G a) = 0)
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G) :
    Assertions Λ f H ↔ ∀ a, Assertions Λ f (G a) := by sorry

end AlgebraicGeometry.IsCurve
