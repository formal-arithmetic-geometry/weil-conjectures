/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero

/-!
# Base change in degree zero along `X ×_K S' ⟶ S'`

For a scheme `X` locally of finite type over a field `K`, the degree-zero base-change property
holds universally for `X ⟶ Spec K`
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_field`): for every base change
`X' = X ×_K S' ⟶ S'`, every quasi-compact quasi-separated `g : T ⟶ S'` and every sheaf `F` on
`T`, the map `p⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism.

Following the proof of blueprint `lem-kun-0f1i`: after the base change to the perfect closure
`K^{perf}` of `K` and the passage to the reduction of `X_{K^{perf}}` — both universal
homeomorphisms, along which étale cohomology and the base-change maps are invariant — the
morphism to the base is flat, locally of finite presentation and has geometrically reduced
fibres, so the degree-zero base change property holds by blueprint `lem-kun-0eys`
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The degree-zero base-change property holds universally for a scheme locally of finite type
over a field. -/
theorem Etale.universalBaseChangeProperty_zero_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] :
    Etale.UniversalBaseChangeProperty Λ a 0 :=
  sorry

end AlgebraicGeometry
