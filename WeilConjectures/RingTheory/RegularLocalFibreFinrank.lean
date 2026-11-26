/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.RegularLocalFibreFinrankComparison
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg

/-!
# Regularity via the fibre of the differentials

For a finite type algebra `S` over a field `k` and a prime `q` with separable residue field
`K = κ(q)`, the local ring `S_q` is regular if and only if `dim_K (K ⊗_S Ω[S/k])` equals the
dimension of `S` at `q`.

## Implementation details

With `R = S_q`, the conormal sequence `m/m² → K ⊗_R Ω[R/k] → Ω[K/k] → 0` is short exact by
separability (Tag 00TU), so `dim_K (K ⊗_S Ω[S/k]) = e + t` with `e = dim_K(m/m²)` and
`t = trdeg_k K`. The dimension of `S` at `q` is `d + t` with `d = dim R`, and `R` is regular if
and only if `e = d`.

## References

* [Stacks, Tag 00TV] (proof)
* [Stacks, Tag 00TU]
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

/-- The cotangent dimension formula at a finite type algebra prime with separable residue field.
-/
theorem regularLocal_iff_fibre_finrank_eq_dimension
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hsep : Algebra.IsSeparableExtension k q.ResidueField) :
    IsRegularLocalRing (Localization.AtPrime q) ↔
      (Module.finrank q.ResidueField
        (q.ResidueField ⊗[S] KaehlerDifferential k S) : WithBot ℕ∞) =
        topologicalKrullDimAt (⟨q, inferInstance⟩ : PrimeSpectrum S) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  obtain ⟨d, r, hd, hr, hpoint⟩ :=
    AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) q
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace, hd,
    fibre_finrank_eq_cotangent_finrank_add k S q hsep r hr, hpoint]
  simp only [Nat.cast_inj, Nat.add_right_cancel_iff]

end Algebra
