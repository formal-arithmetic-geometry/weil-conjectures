/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.MvPolynomial.Basic
import WeilConjectures.RingTheory.RelativeCompleteIntersectionClosedFiberRegularSequence
import WeilConjectures.RingTheory.RegularSequenceFlatClosedFiber

/-! # The Noetherian case of local complete-intersection regularity

Over a Noetherian base, the equations of a relative complete intersection form a regular
sequence in the localization of the polynomial ring at every prime containing them.

## Implementation details

The map `R_p → P_Q` is a flat local map of Noetherian local rings. The equations are regular in
its closed fibre (via base change, Tag 00SS, and the field case, Tag 00SC), and the flat
closed-fibre lifting lemma (Tag 00MG) lifts regularity. For `c = 0` all lists are empty.

## References

* [Stacks, Tag 00SV] (first paragraph of the proof)
* [Stacks, Tags 00SC, 00SS, 00MG]
-/

@[expose] public section

universe u

namespace Algebra

/-- Over a Noetherian base the specified equations are regular at every polynomial prime
containing their ideal. -/
theorem isRegular_localization_of_relativeCompleteIntersection_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime]
    (hQ : Ideal.span (Set.range f) ≤ Q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime Q)
      ((List.ofFn f).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))) := by
  let P := MvPolynomial (Fin n) R
  let p := Q.comap (algebraMap R P)
  let φ := Localization.localRingHom p Q (algebraMap R P) rfl
  have hflat : φ.Flat := RingHom.Flat.localRingHom
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R P)) Q p rfl
  exact (RingTheory.Sequence.isRegular_and_flat_quotient_of_closedFiber φ hflat
    ((List.ofFn f).map (algebraMap P (Localization.AtPrime Q)))
      (isRegular_closedFiber_of_relativeCompleteIntersection f h Q hQ)).1

end Algebra
