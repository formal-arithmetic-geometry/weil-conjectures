/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension

/-!
# Finite algebras over Nagata rings

A finite algebra over a Nagata ring is Nagata; in particular, quotients of Nagata rings are
Nagata.

## Main results

- `finite_over_nagata_is_nagata`

## Implementation details

For a prime `q` of `S` contracting to `p` in `R`, the extension `R/p → S/q` is a finite
extension of domains, so the N-2 property ascends by `isN2_of_finite_domain_extension`.

## References

- Stacks Project, Algebra, Tag 032T (finite case) and Tag 032I.
-/

@[expose] public section

universe u v

/-- The finite-algebra assertion of Stacks Tag 032T, using N-2 ascent (Tag 032I). -/
private theorem finite_nagata (R : Type u) (T : Type v) [CommRing R] [CommRing T]
    [Algebra R T] [Module.Finite R T] (hR : IsNagataRing R) : IsNagataRing T := by
  let : IsNoetherianRing R := hR.1
  refine ⟨?_, ?_⟩
  · exact IsNoetherianRing.of_finite R T
  · intro q hq
    let p : Ideal R := q.comap (algebraMap R T)
    let : p.IsPrime := inferInstance
    let : IsNoetherianRing (R ⧸ p) := IsNoetherianRing.of_finite R (R ⧸ p)
    let : IsScalarTower R (R ⧸ p) (T ⧸ q) :=
      IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
    let : Module.Finite R (T ⧸ q) := inferInstance
    let : Module.Finite (R ⧸ p) (T ⧸ q) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ p) (T ⧸ q)
    exact isN2_of_finite_domain_extension (R ⧸ p) (T ⧸ q)
      (FractionRing (R ⧸ p)) (FractionRing (T ⧸ q))
      Ideal.algebraMap_quotient_injective (hR.2 p)

/-- If `R` is Nagata and `S` is finite as an `R`-algebra, then `S` is Nagata;
quotients of `R` by arbitrary ideals are Nagata as well. -/
theorem finite_over_nagata_is_nagata (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] (hR : IsNagataRing R) :
    IsNagataRing S ∧ ∀ (I : Ideal R), IsNagataRing (R ⧸ I) := by
  exact ⟨finite_nagata R S hR, fun I ↦ finite_nagata R (R ⧸ I) hR⟩
