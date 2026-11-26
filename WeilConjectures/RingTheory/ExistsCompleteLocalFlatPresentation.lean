/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.CompleteLocalMapRegularPresentation

/-!
# Flat presentations of maps of complete Noetherian local rings

A local map of complete Noetherian local rings `A → B` fits into a commutative square with
surjective vertical maps `R → A`, `S → B` and a flat local upper map `R → S` between complete
Noetherian local rings.

## Implementation details

Choose Cohen power-series surjections `q : R → A` and `b : S₀ → B`, and lift `f ∘ q` to a local
map `g : R → S₀` by formal smoothness of power series rings (over `ℚ` in residue characteristic
zero, over `ℤ` otherwise), using that the kernel of `b` is closed. Adjoin variables `yᵢ` to `S₀`
sent to zero in `B`, and send each parameter `xᵢ` of `R` to `g(xᵢ) + yᵢ`. The images of the
parameters of `R` are part of a regular system of parameters of the regular local ring `S`, so
the upper map is flat by the flatness criterion over regular rings.

## References

* [Stacks, Tag 07NN]
-/

@[expose] public section

universe u v

namespace RingHom

/-- A local map of complete Noetherian local rings admits a commutative square with
surjective vertical maps and a flat upper map between complete Noetherian local rings. -/
theorem exists_completeLocal_flat_presentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    ∃ (R S : Type (max u v)) (rR : CommRing R) (rS : CommRing S),
      letI := rR
      letI := rS
      ∃ (lR : IsLocalRing R) (lS : IsLocalRing S),
        letI := lR
        letI := lS
        IsNoetherianRing R ∧ IsNoetherianRing S ∧
        IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
        IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
        ∃ (g : R →+* S) (q : R →+* A) (b : S →+* B),
          IsLocalHom g ∧ IsLocalHom q ∧ IsLocalHom b ∧
          Function.Surjective q ∧ Function.Surjective b ∧
          g.Flat ∧ b.comp g = f.comp q := by
  obtain ⟨R, S, rR, rS, hR, hS, hcR, hcS, q, b, g,
    hq, hlq, hb, hlb, hlg, hcomm, _, _, hflat, _⟩ :=
    exists_complete_local_map_regular_presentation f
  let := rR
  let := rS
  let := hR
  let := hS
  exact ⟨R, S, rR, rS, inferInstance, inferInstance,
    inferInstance, inferInstance, hcR, hcS, g, q, b,
    hlg, hlq, hlb, hq, hb, hflat, hcomm⟩

end RingHom
