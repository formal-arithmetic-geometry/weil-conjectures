/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Artinian.Module
import WeilConjectures.RingTheory.ArtinianSeparableResidueLiftCapture

/-!
# Capturing a separable residue element by a finite étale extension

A separable element of the residue field of `S` over that of an Artinian local ring `D` is the
residue of an element of a finite étale local Artinian `D`-algebra mapping locally to `S`.

## Implementation details

The construction lifts the separable extension of residue fields to a finite étale `D`-algebra
and retracts its base change to `S` using that Artinian local rings are henselian. No flatness of
`D → S` is needed.

## References

* [Stacks, Tag 07FI] (proof)
* [Stacks, Tag 06RS]
* [Stacks, Tag 04GK]
* [Stacks, Tag 04GG]
-/

@[expose] public section

set_option autoImplicit false
universe u v z

namespace Algebra

/-- Let `D → S` be a local map of Artinian local rings and `b` an element of the residue field of
`S` that is separable over the residue field of `D`. Then there are a finite étale local Artinian
`D`-algebra `D'`, a local map `g' : D' → S` over `D`, and `d ∈ D'` with `g'(d)` reducing to `b`. -/
theorem exists_finiteEtale_artinian_residue_lift_core
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (b : IsLocalRing.ResidueField S)
    (hb : IsSeparable (IsLocalRing.ResidueField D) b) :
    ∃ (D' : Type (max u v z)) (_ : CommRing D') (_ : Algebra D D') (g' : D' →+* S),
      IsLocalRing D' ∧ IsArtinianRing D' ∧
      IsLocalHom (algebraMap D D') ∧ IsLocalHom g' ∧
      Etale D D' ∧ Module.Finite D D' ∧
      g'.comp (algebraMap D D') = algebraMap D S ∧
      ∃ d : D', IsLocalRing.residue S (g' d) = b := by
  obtain ⟨D', hD', hDD', g', hlocal, hmap, hg', het, hfin, hcomp, d, hd⟩ :=
    exists_finiteEtale_artinian_residue_lift_capture D S b hb
  let : CommRing D' := hD'
  let : Algebra D D' := hDD'
  let : IsLocalRing D' := hlocal
  let : IsLocalHom (algebraMap D D') := hmap
  let : IsLocalHom g' := hg'
  let : Etale D D' := het
  let : Module.Finite D D' := hfin
  have hart : IsArtinianRing D' := IsArtinianRing.of_finite D D'
  exact ⟨D', hD', hDD', g', hlocal, hart, hmap, hg', het, hfin, hcomp, d, hd⟩

end Algebra
