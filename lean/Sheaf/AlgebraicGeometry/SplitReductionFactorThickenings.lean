/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Factor thickenings for a split reduction

Source: smooth purity blueprint, finite-algebra calculation.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The split reduced factor spectra thicken onto a disjoint open partition.

Source: smooth purity blueprint,
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation.
(blueprint: lem-weil-pbc-split-reduction-factor-thickenings).

Proof: Choose the supplied algebra equivalence and apply Spec. For the finite
product, the factor spectra are pairwise disjoint clopen subschemes covering
its spectrum. Transport these opens to Spec(R / nilradical R), then along the
homeomorphism onto Spec R induced by the quotient. The inverse image of each
transported open under the quotient morphism is the corresponding factor
spectrum. Restricting that quotient closed immersion and composing with this
factor isomorphism gives a surjective closed immersion into the lifted open.
The algebra equivalence is A-linear, so its composite with the structural map
is the specified structural map of D_i. With no factors, the product is the
zero ring and both spectra are empty, giving the same empty covering. -/
theorem exists_split_reduction_factor_thickenings
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, Algebra A (D j)]
    (he : Nonempty ((R ⧸ _root_.nilradical R) ≃ₐ[A] (∀ j, D j))) :
    ∃ (W : Fin r → (Spec (.of R)).Opens),
      (⨆ i, W i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (W i) (W j)) ∧
      ∀ i, ∃ (a : Spec (.of (D i)) ⟶ (W i).toScheme),
        IsClosedImmersion a ∧ Surjective a ∧
          a ≫ (W i).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)) =
            Spec.map (CommRingCat.ofHom (algebraMap A (D i))) := by sorry

end AlgebraicGeometry.Scheme
