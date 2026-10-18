/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.Theorem
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded

/-!
# Base change towards spectra of fields, for arbitrary schemes and complexes

This file extends `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field` (blueprint
`lem-kun-0f1i`, for `X` locally of finite type over `K`) to arbitrary `K`-schemes `X` — the
question is local on `X`, and an affine `X` is the limit of affine schemes of finite type over
`K` (blueprint `lem-kun-0ezt`) — and to bounded below complexes: the derived base change map
`Lf'^* Rg_* F ⟶ Rh_* Le^* F` is an isomorphism for every `F ∈ D⁺(T_ét, Λ)`
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_field`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0f1i`, derived form: for an arbitrary scheme `X` over a field `K` and
`Λ` finite with exponent invertible in `K`, the derived base change map
`Lf'^* Rg_* F ⟶ Rh_* Le^* F` of the diagram `X ×_K S' ⟵ X ×_K T` over `S' ⟵ T` is an
isomorphism for every bounded below `F`. -/
theorem Etale.isIso_derivedBaseChangeMap_of_field [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_sq₁ : IsPullback p f' a b) (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (sq₂ : IsPullback h e f' g)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [F.IsGE n] :
    IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq₂.w.symm)).app F) :=
  sorry

end AlgebraicGeometry
