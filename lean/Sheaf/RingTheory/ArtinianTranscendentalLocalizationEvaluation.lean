/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Artinian.Defs
import Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian

/-!
# A component of the transcendental polynomial localization argument

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FI.
-/

@[expose] public section
set_option autoImplicit false
universe u v z
namespace Algebra

/-- The flat local evaluation map from the transcendental polynomial localization.
Source: Stacks Project, Smoothing Ring Maps, Tag 07FI, lines 2642--2675.
(blueprint: lem-weil-pbc-artinian-transcendental-localization-core-evaluation)
Proof: Every polynomial outside P evaluates outside m_S, hence to a unit.
The localization universal property constructs g_0 : D[t]_P -> S. Its
contraction of m_S is the maximal ideal of D[t]_P, so g_0 is local.
The universal property gives the factorization over D, and t/1 maps to x.
As in the structural argument, transcendence identifies P with m_D[t];
thus the closed fibre of D -> D[t]_P is F(t), where F = D/m_D.
Apply the Noetherian fibre flatness criterion to D -> D[t]_P -> S with
module M = S, finite over itself: M is flat over D by hflat and its
closed fibre is flat over the field F(t). Hence g_0 is flat. Compose
with the canonical ULift down ring equivalence to obtain g'. This retains
locality, flatness, the factorization and the image of t/1. For D a field
this is precisely extension of evaluation from D[t] to its fraction field. -/
theorem localization_transcendental_evaluation
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat) (x : S)
    (hx : Transcendental (IsLocalRing.ResidueField D) (IsLocalRing.residue S x)) :
    let P : Ideal (Polynomial D) :=
      (IsLocalRing.maximalIdeal S).comap (Polynomial.eval₂RingHom (algebraMap D S) x)
    letI : P.IsPrime := inferInstance
    let T := ULift.{max u v z} (Localization.AtPrime P)
    ∃ g' : T →+* S, IsLocalHom g' ∧ g'.Flat ∧
      g'.comp (algebraMap D T) = algebraMap D S ∧ x ∈ Set.range g' := by sorry


end Algebra
