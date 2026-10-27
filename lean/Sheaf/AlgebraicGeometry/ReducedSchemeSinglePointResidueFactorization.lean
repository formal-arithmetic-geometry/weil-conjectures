/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField

/-!
# Reduced schemes with image contained in a point

Source: Stacks Project, Morphisms, Tag 0H1M, lemma-factor-through-point
(blueprint: lem-sfb-reduced-scheme-single-point-residue-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism from a reduced scheme with image contained in `{x}` factors through
`Spec κ(x)`. The source can be empty and need not be quasi-compact or Noetherian.

Source: Stacks Project, Morphisms, Tag 0H1M, lemma-factor-through-point
(blueprint: lem-sfb-reduced-scheme-single-point-residue-factorization).

Proof:
1. Choose an affine neighbourhood `U = Spec A` of `x` and factor `f` through `U`,
since its inverse image is all of `Y`. The affine-open point and stalk identifications
(lem-weil-pbc-affine-open-spec-points, lem-weil-pbc-affine-open-stalk-localization)
identify `x` with a prime `p` and its stalk with `A_p`. Cover `Y` by arbitrary affine
opens `V_i = Spec B_i`. Reducedness makes each `B_i` reduced. Write `φ_i : A → B_i`
for the induced ring map. No finite subcover is chosen.
2. For `a ∈ p`, locality of stalk maps and compatibility with germs imply that
`φ_i(a)` vanishes in every residue field of `V_i`. Each affine `V_i` is quasi-compact
(lem-weil-pbc-affine-scheme-qcqs). Thus
lem-weil-pbc-qc-scheme-vanishing-section-nilpotent makes `φ_i(a)` nilpotent, hence zero
by reducedness. Therefore `p` is contained in the kernel of `φ_i`.
3. For `s ∉ p`, its germ at `x` is a unit, so the germ of `φ_i(s)` is a unit at every
point of `V_i`. By the affine stalk identification, `φ_i(s)` lies in no prime of `B_i`.
Clause (ii) of lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact makes it a unit.
This includes `B_i` the zero ring, whose spectrum is empty and whose element is a unit.
4. Clause (d) of lem-weil-pbc-prime-residue-field-algebra gives a ring map
`κ(p) → B_i` extending `φ_i`. Clause (2) of lem-weil-pbc-spec-field-point-residue-field
identifies `κ(p)` with `κ(x)` and its canonical point map with Spec of the residue map
on `U`. Affine-spectrum duality gives `h_i : V_i → Spec κ(x)` with composite `f|V_i`.
5. Cover each intersection `V_i ∩ V_j` by affine opens `Spec C`. The two restricted
ring maps `κ(p) → C` agree on `A`. Clause (c) of
lem-weil-pbc-prime-residue-field-algebra makes them equal. Affine-spectrum duality
and the equality clause of lem-weil-pbc-scheme-morphism-gluing then show agreement
on the entire intersection, without requiring it to be affine or quasi-compact.
6. Apply lem-weil-pbc-scheme-morphism-gluing to glue the `h_i` to `h`. Equality of
its composite with `f` is local on this open covering, hence holds globally. For empty
`Y` use the empty covering and the same gluing and equality statements. The coverings
may be infinite; no global quasi-compactness or Noetherian assumption was used. -/
theorem exists_factor_through_residueField_of_isReduced_of_range_subset_singleton
    {Y X : Scheme.{u}} [IsReduced Y] (f : Y ⟶ X) (x : X)
    (himage : Set.range f ⊆ {x}) :
    ∃ h : Y ⟶ Spec (X.residueField x), h ≫ X.fromSpecResidueField x = f := by
  sorry

end AlgebraicGeometry
