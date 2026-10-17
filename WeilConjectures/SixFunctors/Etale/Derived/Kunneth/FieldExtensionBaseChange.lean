/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.LimitBaseChange

/-!
# Higher direct images commute with base change along field extensions

Let `L/K` be a field extension and `g : T ⟶ S` a quasi-compact quasi-separated morphism of
schemes over `K`. For every sheaf `F` on `T` whose geometric stalks are torsion of orders
invertible in `K`, the base-change map `R^q g_* F |_{S_L} ⟶ R^q g_{L,*} (F|_{T_L})` is an
isomorphism (blueprint `lem-kun-0f1c`, Stacks 0F1C). After passing to perfect closures (a
universal homeomorphism does not change the étale sites) the extension is separable, hence a
filtered colimit of smooth algebras, and smooth base change along limits
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth`) applies.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_fieldExtension`

## References

- Stacks Project, Lemma 59.89.4, <https://stacks.math.columbia.edu/tag/0F1C>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0f1c`: Direct image commutes with base change along field extensions.

Let `L/K` be a field extension, `σ : S ⟶ Spec K` a scheme over `K` and `g : T ⟶ S` a
quasi-compact quasi-separated morphism. Let `S' = S ×_K L` (the Cartesian square `hS`) and
`T' = T ×_S S'` (the Cartesian square `sq`). For every sheaf `F` of `Λ`-modules on `T` whose
geometric stalks are torsion of orders invertible in `K`, the base-change map
`R^q g_* F |_{S'} ⟶ R^q h_* (F|_{T'})` is an isomorphism in every degree `q`. -/
@[stacks 0F1C]
theorem Etale.isIso_baseChangeHomologyMap_of_fieldExtension {K L : Type u} [Field K] [Field L]
    [Algebra K L] {S T S' T' : Scheme.{u}} (σ : S ⟶ Spec (.of K)) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] (p : S' ⟶ S) (σ' : S' ⟶ Spec (.of L))
    (hS : IsPullback p σ' σ (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {e : T' ⟶ T} {h : T' ⟶ S'} (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

end AlgebraicGeometry
