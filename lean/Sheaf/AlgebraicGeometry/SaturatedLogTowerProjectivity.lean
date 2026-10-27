/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Projectivity of a fixed saturated logarithmic blowup tower

Source: ILO VIII 3.3.8--3.3.9; Stacks Tags 01N2, 01Q2, 01PU, 0BCL, 0C4P, 087S
(blueprint: lem-per-saturated-log-tower-projectivity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every fixed finite saturated log blowup tower over a quasi-compact fs log scheme
which immerses in finite projective space over an affine base has H-projective composite.
No log regularity, integralness, or terminal freeness is assumed.

Source: ILO VIII 3.3.8--3.3.9; Stacks 01N2, 01Q2, 01PU, 0BCL, 0C4P, 087S
(blueprint: lem-per-saturated-log-tower-projectivity).

Proof:
1. Identify projective space over Spec A with Proj A[T_0,...,T_n] using affine Proj
scalar extension. Shrink the immersion of the quasi-compact initial scheme to a closed
immersion into a quasi-compact open of this Proj. A sufficiently divisible twist on
that open is ample and invertible; its closed pullback gives an ample invertible module
on the initial scheme. Local Noetherianity is already part of every fs log scheme.
2. For each arrow choose strict affine etale charts P and finite nonempty center E.
The fine blowup has charts C tensor_Z[P] Z[Q_e]. Inside Z[P^gp], the algebra
Z[P][(z^h/z^e) : h in E] is Z[Q_e], by the monomial basis. The identifications respect
overlap localizations. Thus this fine blowup is the base change of the toric ordinary
blowup of the finite monomial ideal (z^e). It is proper; saturation is finite by the
coherent log ideal chart construction. Properness of each saturated arrow descends
along the strict etale fpqc cover.
3. On the saturated charts the sheaf of generators of the pulled-back log ideal gives
the canonical tautological invertible module. Its frames have transitions z^(f-e),
and its generating sections have precisely these affine charts as nonvanishing loci.
The chart lifting criterion and tautological polarization theorem give relative
ampleness and generator-independent descent isomorphisms satisfying the cocycle.
Polarized etale descent glues this module; fpqc descent gives relative ampleness.
4. The initial scheme is qcqs, and properness inductively makes all subsequent
schemes quasi-compact; local Noetherianity makes them quasi-separated. Properness
and relative ampleness make every arrow projective in the projective-bundle sense.
Compose these factorizations over the qcqs initial base. The ample module from step 1
converts bundle projectivity to H-projectivity. The equations on p identify this
composite with the supplied terminal map. At length zero p is the identity, whose
projective-bundle factorization is P(O)=X. Empty schemes and whole-monoid centers
cause no exception. -/
theorem saturatedLogTower_isHProjective
    (T : SaturatedLogBlowupTower.{u}) [CompactSpace (T.level 0).scheme]
    (p : ∀ i : Fin (T.length + 1), EtaleLogHom (T.level i) (T.level 0))
    (hp0 : p 0 = EtaleLogHom.id (T.level 0))
    (hp : ∀ i : Fin T.length, (T.arrow i).CompEq (p i.castSucc) (p i.succ))
    (A : Type u) [CommRing A]
    (hqp : ∃ (n : ℕ) (i : (T.level 0).scheme ⟶
      ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))), IsImmersion i) :
    IsHProjective (p (Fin.last T.length)).base := by sorry

end AlgebraicGeometry
