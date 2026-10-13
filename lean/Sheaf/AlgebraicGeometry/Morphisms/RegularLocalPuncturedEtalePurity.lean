/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Purity for the punctured spectrum of a regular local ring

Source: Stacks Project, Tag 0BMA, `pione-lemma-purity-regular`.
(blueprint: lem-sbc-regular-local-punctured-etale-purity)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Finite etale covers of the punctured spectrum of a regular local ring of dimension
at least two extend to the whole local spectrum.

Source: Stacks Project, Tag 0BMA, `pione-lemma-purity-regular`, assertion (1).
(blueprint: lem-sbc-regular-local-punctured-etale-purity)

Proof: Induct on the dimension d, which is finite for a Noetherian local ring.
A regular local ring is normal. For a nonempty connected cover, Tag 0BM9
constructs its finite normal extension algebra B as the integral closure of
A in the finite separable function-field extension of the cover. It suffices
to prove B etale; disconnected covers are finite disjoint unions of these.
For d = 2, going down gives dimension two at every maximal ideal of B.
A normal two-dimensional local ring is Cohen-Macaulay. The local
flatness criterion over the regular base then makes these localizations flat,
and hence the finite algebra flat. The discriminant criterion, or Tag 0BJH,
makes it etale. For d > 2 choose a parameter f outside the square of the
maximal ideal. The quotient by f is regular of dimension d - 1. Restrict the
cover to its punctured spectrum; induction extends this restriction. A regular
system of parameters gives depth A = d, hence depth A is at least three.
Together with the nonzerodivisor f, this verifies the depth hypothesis of the
lifting criterion Tag 0BLM, which extends the original cover. Empty covers
extend to the empty scheme. The condition on U identifies it exactly with
this punctured spectrum, independently of the chosen representation of U. -/
theorem exists_finite_etale_extension_of_regular_local_punctured_spectrum
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q] :
    ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsFinite r ∧ Etale r ∧
      ∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q := by sorry

end AlgebraicGeometry.Scheme
