/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.PopescuAuxiliaryAlgebraLocalizations
import WeilConjectures.RingTheory.PopescuDelocalizeHeightZeroData
import WeilConjectures.RingTheory.PopescuDelocalizeWeak
import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.SingularIdealLocalizationSmooth

/-!
# Delocalizing a Popescu resolution at a prime of height zero

At a minimal prime `q` over the extended singular ideal with `dim Λ_q = 0`, a resolution of the
localized problem gives a resolution of the original one.

## Implementation details

The images of generators `a_i` of the singular ideal are nilpotent in `Λ_q`, so `λ α(a_i)^N = 0`
for some `λ ∉ q` (elementwise nilpotence, without assuming `Λ_q` Artinian). The weak
delocalization lemma (Tag 07F9) gives `A → C → Λ`, and the auxiliary algebra
`B = A[x_k, y_i, z, t_ij] / (f_j - ∑ y_i t_ij, z y_i)` maps to `Λ` by `y_i ↦ α(a_i)^N`, `z ↦ λ`;
its localizations at `z c'` and `a_l y_l` are smooth, which gives the resolution.

The tensor factors are reversed by the canonical commutativity isomorphism, so `A_p` is
`R_p ⊗[R] A`; the local algebra structure on `Λ_q` is the canonical one, and `dim Λ_q = 0` is
`ringKrullDim Λ_q = 0`.

## References

* [Stacks, Tag 07FA]
* [Stacks, Tag 07F9]
-/

@[expose] public section

universe u v t

open scoped TensorProduct

namespace Algebra

/-- A resolution at a minimal prime over the extended singular ideal descends from the
local problem when the target localization has dimension zero. -/
theorem canBePopescuResolved_of_local_height_zero
    {R : Type u} {A : Type v} {Λ : Type t}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)
    (hlocal :
      letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
      CanBePopescuResolved
        (Algebra.TensorProduct.lift
          (Algebra.ofId (Localization.AtPrime (q.asIdeal.under R))
            (Localization.AtPrime q.asIdeal))
          ((IsScalarTower.toAlgHom R Λ (Localization.AtPrime q.asIdeal)).comp α)
          (fun _ _ => Commute.all _ _))
        ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal), inferInstance⟩)
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0) :
    CanBePopescuResolved α q := by
  obtain ⟨B, _instB, _algB, β, γ, hfp, hcomp, hle, hnot⟩ :=
    exists_popescu_resolution_data_of_local_height_zero α q hminimal hlocal hdim
  exact ⟨B, inferInstance, inferInstance, β, γ, hfp, hcomp, hle, hnot⟩

end Algebra
