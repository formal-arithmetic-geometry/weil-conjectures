/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

/-!
# Admissible condensed coefficients for the fixed coefficient prime

Source: the current blueprint `def-sf-setting.md`, opening coefficient convention, with
Wei Yang #1412, item 3, as recorded in the released repair note
(blueprint: def-pur-admissible-condensed-ring).

The global coefficient datum fixes the prime, distinct from the geometric characteristic.
Finite coefficients range over all finite commutative rings killed by a positive power of
that prime. The other coefficients use the published continuous-map and finite-subextension
constructions. Membership is invariant under isomorphism of unital ring objects.

`PadicAlgCl` is the representative algebraic closure used by the recorded condensed-ring
interfaces. Finite intermediate fields in it represent all finite extensions in the chosen
algebraic closure. The distinguished integral reductions remain the existing rings
`Padic.coefficientExtensionRing`; they do not restrict the finite coefficient clause.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Admissibility for the prime fixed by the global coefficient datum: arbitrary finite
commutative discrete prime-primary rings, continuous rings of integers and fields of finite
extensions, and the finite-subextension-valued condensed algebraic closure.

The datum `c` includes primality and `c.l ≠ D.p`. Annihilation means that a positive power of
`c.l` is zero in the unital ring, hence kills every element. The finite carrier can be taken
in `Type 0` without restricting its isomorphism class. The ambient profinite and geometric
universes are independent. All isomorphisms below are in the category of ring objects.

Source: `def-sf-setting.md`, opening paragraph, and Wei Yang #1412, item 3 (arbitrary finite
commutative prime-primary coefficients, with the DVR quotients distinguished for reduction).
(blueprint: def-pur-admissible-condensed-ring). -/
def IsAdmissibleCoefficientFor
    {D : WeilConjectures.FiniteFieldDatum.{v}} (c : D.CoefficientDatum)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] : Prop :=
  (∃ (A : Type) (_hA : CommRing A) (_hfin : Finite A)
      (_htop : TopologicalSpace A) (_hd : DiscreteTopology A) (_hr : IsTopologicalRing A),
    (∃ r : ℕ, 1 ≤ r ∧ (c.l ^ r : A) = 0) ∧
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} A))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField c.l,
    Nonempty (Λ ≅ Mon.mk (Profinite.padicIntegersRingObj.{u} c.l E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField c.l,
    Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E))) ∨
  Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} c.l))

end AlgebraicGeometry.ProEtale.CondensedRing
