/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.Smooth.Basic
import Sheaf.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent
import Sheaf.LinearAlgebra.Matrix.LeftInverseMinors

/-!
# Smooth localization at a strictly standard element

Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07CA, first paragraph of the proof
(blueprint: lem-weil-pbc-strictly-standard-localization-smooth).
-/

@[expose] public section

universe u v

namespace Algebra

/-- Localization at a strictly standard element of a finitely presented algebra is smooth.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07CA, first paragraph
(blueprint: lem-weil-pbc-strictly-standard-localization-smooth).

Proof (the six steps of the DAG node):
1. Choose the presentation `P → A`, with kernel `I = (f₁, …, fₘ)`, and the integer `c`
from `def-weil-pbc-strictly-standard-element`. By
`lem-weil-pbc-polynomial-ring-kahler-basis`, the differentials of the variables form a basis
of the base-changed differential module. The conormal differential composed with the map
`A^c → I/I²` taking the standard basis to the first `c` relation classes has Jacobian matrix.
2. The first strictly standard condition expresses `a` as a linear combination of the
maximal minors of that matrix. By `lem-weil-pbc-matrix-left-inverse-minors`, there is a
matrix `B` whose product with the Jacobian is `a` times the identity.
3. Lift `a` to the polynomial ring. The second condition puts its product with each remaining
relation in `(f₁, …, f_c) + I²`. After localizing, the first `c` relation classes therefore
generate `(I/I²)_a` (`def-weil-pbc-module-localization-away`).
4. Localize the maps using `lem-weil-pbc-localization-module-tensor`. Since `a` is now a unit,
rescaling `B` gives a left inverse for the map from `A_a^c` to the localized differential
module. The surjection from step 3 is consequently an isomorphism, giving a left inverse
for the localized conormal differential itself.
5. Apply `lem-weil-pbc-principal-localization-naive-cotangent`: adjoining a variable `y`
with relation `hy - 1`, for a lift `h` of `a`, presents `A_a`. Under its conormal and
differential isomorphisms, the differential is the direct sum of the map in step 4 and
multiplication by `a`. Combining their left inverses splits this presentation's conormal map.
6. The new presentation has finitely many generators and relations. By
`lem-weil-pbc-presentation-split-conormal-smooth`, its split conormal map implies that
`A_a` is smooth over `R`. Its algebra structure is the composite `R → A → A_a`. -/
theorem smooth_localizationAway_of_isStrictlyStandardElement
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (a : A) (ha : IsStrictlyStandardElement (R := R) a) :
    Smooth R (Localization.Away a) := by
  sorry

end Algebra
