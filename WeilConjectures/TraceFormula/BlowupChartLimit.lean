/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitSmoothSurface
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationSmoothSurface
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.RingTheory.TangentConeInitialForms
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The charts of the blow-up of the strict localization of a smooth surface

Let `S` be a smooth surface over an algebraically closed field `k` and `t` a `k`-point of `S`,
with strict localization `T = Spec R`, `R = 𝒪^{sh}_{S,t}` (blueprint
`sk-lem-tf-blowup-restriction`). Then `R` is a regular local ring of dimension `2` with residue
field `k`, and there is a regular system of parameters `(x₀, y₀)` of `R`, coming from étale
coordinates of `S` at `t`, such that for every `a ∈ k` every open subscheme
`Spec (R[T]/(xT - y))[1/u]` of the chart of the blow-up of `T` at `t` for `x = x₀ + a y₀`,
`y = y₀` is an étale limit with affine transition maps of smooth `k`-surfaces (blueprint
`det-tf-blowup-configuration` (1)): it is the base change to `T` of the corresponding chart of the
blow-up of an affine étale neighbourhood `V` of `t` in `S`, which is étale over the affine plane,
and `T` is the limit of the affine étale neighbourhoods of `t` over `V`.

## Main results

- `AlgebraicGeometry.Scheme.exists_isEtaleLimitOfSmoothSurfaces_blowupChart`: the charts of the
  blow-up are étale limits of smooth surfaces.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Over (Spec (.of k)))
  (t : Spec (.of k) ⟶ S.left)

variable [SmoothOfRelativeDimension 2 S.hom]

/-- **The charts of the blow-up of the strict localization of a smooth surface are étale limits
of smooth surfaces** (blueprint `det-tf-blowup-configuration` (1), in a chart). There is a
regular system of parameters `(x₀, y₀)` of `R = 𝒪^{sh}_{S,t}` such that for every `a ∈ k` and
every `u` in the chart `R[T]/(xT - y)`, `x = x₀ + a y₀`, `y = y₀`, of the blow-up of `Spec R` at
its closed point, the `k`-scheme `Spec (R[T]/(xT - y))[1/u]` is an étale limit of smooth
surfaces. -/
theorem exists_isEtaleLimitOfSmoothSurfaces_blowupChart (ht : t ≫ S.hom = 𝟙 _) :
    letI := strictHenselizationAlgebra S t
    ∃ x₀ y₀ : strictHenselization t,
      maximalIdeal (strictHenselization t) = Ideal.span {x₀, y₀} ∧
      ∀ (a : k) (u : blowupChart (x₀ + algebraMap k (strictHenselization t) a * y₀) y₀),
        IsEtaleLimitOfSmoothSurfaces (Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap k (Localization.Away u))))) :=
  sorry

end AlgebraicGeometry.Scheme
