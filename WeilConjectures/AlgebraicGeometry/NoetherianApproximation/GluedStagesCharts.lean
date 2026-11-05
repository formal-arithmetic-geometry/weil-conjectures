/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.GluingStages
public import WeilConjectures.AlgebraicGeometry.OpensGlueData

/-!
# Chart maps of subrings of section rings

Let `U` be an open of a scheme `S` and `A ⊆ Γ(S, U)` a subring. For every open `W ≤ U` the
inclusion `A ⊆ Γ(S, U) ⟶ Γ(S, W)` induces a morphism `W ⟶ Spec A`
(`AlgebraicGeometry.Scheme.subringChart`). These are the chart maps from `S` to the charts of
the finite-type stages of a finite affine gluing presentation.

If `U` is affine, the chart maps are *epimorphic towards affine schemes* on the opens
`⋃ᵢ D(kᵢ)` of `Spec A` (`AlgebraicGeometry.Scheme.chartLift_cancel`): two morphisms out of
`⋃ᵢ D(kᵢ) ⊆ Spec A` into an affine scheme agree as soon as they agree on `⋃ᵢ D_S(kᵢ) ⊆ S`.
This is the geometric form of the fact that `A[1/k] → Γ(S, D(k)) = Γ(S, U)[1/k]` is injective
(localization is exact). Moreover a morphism `⋃ᵢ D_S(kᵢ) ⟶ Spec R` extends to `⋃ᵢ D(kᵢ)` as soon
as on every `D_S(kᵢ)` it is given by sections lying in `A[1/kᵢ]`
(`AlgebraicGeometry.Scheme.exists_chartLift_comp_eq`), and we have a criterion for the image of
such an extension (`AlgebraicGeometry.Scheme.range_subset_iSup_basicOpen`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-! ### Basic opens of spectra -/

/-- The basic open `D(r)` of `Spec R`, as an open of the scheme `Spec R`. -/
def specBasicOpen {R : CommRingCat.{u}} (r : R) : (Spec R).Opens :=
  PrimeSpectrum.basicOpen r

variable {U : S.Opens}

/-! ### Basic opens -/

section BasicOpen

variable (A : Subring Γ(S, U)) (x : A)

variable {A x}

end BasicOpen

/-! ### Finite unions of basic opens -/

section iSup

variable {A : Subring Γ(S, U)} {σ : Type*} (k : σ → A)

end iSup

end AlgebraicGeometry.Scheme
