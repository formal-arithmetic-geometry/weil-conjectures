/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Henselian

/-!
# Étale retractions from simple-root lifting

Source: Stacks Project, Algebra, Lemma Tag 04GG, implication (1) ⇒ (8)
(blueprint: lem-weil-pbc-root-lifting-etale-retraction).
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace IsLocalRing

/-- A local ring in which simple residue roots of monic polynomials lift admits a unique
retraction from an étale algebra through a prime with trivial residue field extension.

Source: Stacks Project, Algebra, Lemma Tag 04GG, proof of (1) ⇒ (8), using Tags 00UE and 06RR.
(blueprint: lem-weil-pbc-root-lifting-etale-retraction).

Proof (the six steps of the DAG node):
1. The residue-field isomorphism gives a surjective R-algebra map ρ : S → κ with kernel q
   (`def-weil-residue-field`). Two surjective R-algebra maps to κ with kernel q agree,
   since any R-algebra automorphism of κ is the identity. Thus a retraction has maximal
   ideal preimage q exactly when its reduction is ρ.
2. By `lem-weil-pbc-etale-locally-standard` (Stacks 00UE), choose g outside q and a standard
   étale presentation S_g ≅ C = R[t][Y]/(f, Yh - 1), with f monic and f' p₁ + f p₂ = h^n.
3. Extend ρ uniquely to S_g and transport it to ρ_C. Localization gives a bijection
   between maps C → R reducing to ρ_C and retractions S → R with maximal ideal preimage q:
   a retraction sends g to a unit, and equality of the reductions is checked on S.
4. Put a₀ = ρ_C(t). By `lem-weil-pbc-standard-etale-pair-maps`, f̄(a₀) = 0 and h̄(a₀) ≠ 0.
   Reduce the standard étale identity and evaluate at a₀ to get f̄'(a₀) ≠ 0.
5. Apply the stated root-lifting hypothesis to obtain a root a of f reducing to a₀.
   Then h(a) has nonzero residue, so is a unit. The universal property in
   `lem-weil-pbc-standard-etale-pair-maps` gives a map C → R sending t to a; its reduction
   is ρ_C since maps out of C are determined by t. Step 3 gives the required retraction.
6. Two such retractions correspond to maps C → R sending t to roots a₁, a₂ with the same
   residue a₀. Since f'(a₁) is a unit, `lem-weil-pbc-simple-root-uniqueness` (Stacks 06RR)
   gives a₁ = a₂. Maps out of C are determined by t, and step 3 gives equality on S.
-/
theorem existsUnique_algHom_of_monic_simple_root_lifting_etale
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    (hroot : ∀ f : Polynomial R, f.Monic → ∀ a₀ : ResidueField R,
      Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ f.derivative ≠ 0 →
        ∃ a : R, f.IsRoot a ∧ residue R a = a₀)
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hres : Function.Bijective
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap
        (⟨q, inferInstance⟩ : Spec (.of S))).hom) :
    ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap τ.toRingHom = q := by
  sorry

end IsLocalRing
