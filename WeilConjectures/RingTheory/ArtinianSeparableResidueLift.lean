/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.ArtinianSeparableResidueLiftCore
import WeilConjectures.RingTheory.ArtinianSeparableResidueLiftFlat

/-!
# Lifting a separable residue element across a flat map of Artinian local rings

A separable element `b` of the residue field of `S`, for a flat local map `D → S` of Artinian
local rings, lies in the residue image of a finite étale local Artinian `D`-algebra `D'` with a
flat local map `D' → S` over `D`.

## Implementation details

With `F`, `K` the residue fields of `D`, `S` and `E = F(b)`, the finite separable extension
`E/F` lifts to a finite étale local `D`-algebra `D'` (Artinian local rings are henselian). The
inclusion `E → K` gives a surjection `S ⊗[D] D' → K`, and henselian étale retraction yields
`g' : D' → S` inducing `E → K`. Flatness of `g'` follows from the Noetherian fibre flatness
criterion, since the closed fibre of `D → D'` is the field `E`. It is not asserted that a
chosen lift of `b` itself lies in the image; removing its nilpotent error is a separate
Frobenius argument.

## References

* [Stacks, Tag 07FI]
* [Stacks, Tag 06RS]
* [Stacks, Tag 04GK]
* [Stacks, Tag 04GG]
* [Stacks, Tag 00MP]
-/

@[expose] public section

set_option autoImplicit false
universe u v z

namespace Algebra

/-- A separable element of the target residue field can be captured by a finite étale
local Artinian extension of the source, with a flat local map to the target. -/
theorem exists_finiteEtale_artinian_residue_lift
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat) (b : IsLocalRing.ResidueField S)
    (hb : IsSeparable (IsLocalRing.ResidueField D) b) :
    ∃ (D' : Type (max u v z)) (_ : CommRing D') (_ : Algebra D D') (g' : D' →+* S),
      IsLocalRing D' ∧ IsArtinianRing D' ∧
      IsLocalHom (algebraMap D D') ∧ IsLocalHom g' ∧
      Etale D D' ∧ Module.Finite D D' ∧ g'.Flat ∧
      g'.comp (algebraMap D D') = algebraMap D S ∧
      ∃ d : D', IsLocalRing.residue S (g' d) = b := by
  obtain ⟨D', hD', hDD', g', hlocal, hart, hmap, hg', het, hfin, hcomp, d, hd⟩ :=
    exists_finiteEtale_artinian_residue_lift_core D S b hb
  let : CommRing D' := hD'
  let : Algebra D D' := hDD'
  let : IsLocalRing D' := hlocal
  let : IsArtinianRing D' := hart
  let : IsLocalHom (algebraMap D D') := hmap
  let : IsLocalHom g' := hg'
  let : Etale D D' := het
  let : Module.Finite D D' := hfin
  have hflat' : g'.Flat :=
    flat_of_finiteEtale_artinian_residue_lift_core D S hflat D' g' hcomp
  exact ⟨D', hD', hDD', g', hlocal, hart, hmap, hg', het, hfin, hflat', hcomp, d, hd⟩

end Algebra
