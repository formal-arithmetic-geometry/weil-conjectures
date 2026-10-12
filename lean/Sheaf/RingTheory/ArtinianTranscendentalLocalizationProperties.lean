/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Artinian.Defs

/-!
# A component of the transcendental polynomial localization argument

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FI.
-/

@[expose] public section
set_option autoImplicit false
universe u v z
namespace Algebra

/-- The structural properties of the transcendental polynomial localization.
Source: Stacks Project, Smoothing Ring Maps, Tag 07FI, lines 2642--2675.
(blueprint: lem-weil-pbc-artinian-transcendental-localization-core-structural)
Proof: Write F = D/m_D and K = S/m_S. Reduction of evaluation factors through
F[t] -> K. Transcendence makes this map injective, so its kernel in D[t] is
exactly m_D[t], and therefore P = m_D[t]. Since D is Artinian it is Noetherian
and m_D is nilpotent. Consequently D[t]_P is Noetherian and local, and its
maximal ideal m_D D[t]_P is nilpotent. A Noetherian local ring with nilpotent
maximal ideal is Artinian. The contraction of this maximal ideal to D is m_D,
so D -> D[t]_P is local. The polynomial algebra is smooth and localization
makes its structure map essentially smooth. Transport all properties across
the canonical ULift ring equivalence. The flatness assumption is not needed
for this component. In the field case the localization is F(t), as expected. -/
theorem localization_artinian_transcendental_properties
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat) (x : S)
    (hx : Transcendental (IsLocalRing.ResidueField D) (IsLocalRing.residue S x)) :
    let P : Ideal (Polynomial D) :=
      (IsLocalRing.maximalIdeal S).comap (Polynomial.eval₂RingHom (algebraMap D S) x)
    letI : P.IsPrime := inferInstance
    let T := ULift.{max u v z} (Localization.AtPrime P)
    IsLocalRing T ∧ IsArtinianRing T ∧ IsLocalHom (algebraMap D T) ∧
      EssentiallySmooth D T := by sorry


end Algebra
