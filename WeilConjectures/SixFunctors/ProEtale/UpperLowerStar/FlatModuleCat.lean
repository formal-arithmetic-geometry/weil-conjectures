/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.KFlat

/-!
# The pullback of pro-étale sheaves of modules preserves flatness

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`.
For a noetherian ring `Λ` and a morphism of schemes `g`, the pullback `g^*` of pro-étale sheaves
of `Λ`-modules preserves flat sheaves: `g^*` is the pullback along the base change functor,
which is representably flat and cover-preserving
(`AlgebraicGeometry.Scheme.ProEt.coverPreserving_overPullback`), so this is
`CategoryTheory.flat_sheafPullback_obj`.

## Main results

- `AlgebraicGeometry.ProEtale.upperStarPreservesFlat_moduleCat`: the instance
  `AlgebraicGeometry.ProEtale.UpperStarPreservesFlat (ModuleCat Λ)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]

set_option synthInstance.maxHeartbeats 400000 in
-- the instances `WEqualsLocallyBijective` and `HasSheafCompose` on the small pro-étale sites
-- take long to synthesize
/-- **The pullback of pro-étale sheaves of `Λ`-modules preserves flatness**, for a noetherian
ring `Λ`. -/
instance upperStarPreservesFlat_moduleCat :
    ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} Λ) where
  preservesFlat g := by
    have := MorphismProperty.Over.representablyFlat_pullback @WeaklyEtale g
    exact ⟨fun hF ↦ flat_sheafPullback_obj (ProEt.coverPreserving_overPullback g) hF⟩

end AlgebraicGeometry.ProEtale
