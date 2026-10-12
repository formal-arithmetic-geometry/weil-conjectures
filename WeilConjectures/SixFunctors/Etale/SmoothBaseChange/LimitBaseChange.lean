/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived

/-!
# Base change along limits of smooth schemes and along field extensions

Two consequences of the smooth base change theorem, recorded for the derived base change map
`AlgebraicGeometry.Etale.baseChange` on bounded below complexes whose cohomology sheaves are
torsion of orders invertible on the base:

- base change along a directed limit `S' = lim Sᵢ` of smooth quasi-compact quasi-separated
  `S`-schemes with affine transition morphisms
  (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_isLimit_of_smooth`, blueprint
  `lem-kun-0f09`): at each stage this is smooth base change, and one passes to the limit by the
  continuity of higher direct images;
- base change along an arbitrary extension of fields `L/K`, for a quasi-compact
  quasi-separated morphism of `K`-schemes
  (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_field`, blueprint `lem-kun-0f1c`): the
  purely inseparable part is a universal homeomorphism, and a separable extension is a directed
  limit of smooth algebras.

Both are lemmas of the subsection `sk-prop-sf-kunneth-ordinary` of the blueprint; their proofs
are not formalised here.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0f09`: Smooth base change for limits of smooth schemes.

Let `S' = lim Sᵢ` be a directed inverse limit of schemes `Sᵢ` which are smooth, quasi-compact and
quasi-separated over `S`, with affine transition morphisms, let `f : X ⟶ S` be quasi-compact and
quasi-separated, and consider a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

Then the derived base change map `g^* Rf_* E ⟶ Rf'_* g'^* E` is an isomorphism for every
`E ∈ D⁺(X_ét, Λ)` whose cohomology sheaves are torsion of orders invertible on `S`. -/
theorem Etale.isIso_baseChange_app_of_isLimit_of_smooth {S X : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] {I : Type u} [Preorder I] [IsCodirectedOrder I]
    [Nonempty I] (D : I ⥤ Over S) [∀ i, Smooth (D.obj i).hom] [∀ i, QuasiCompact (D.obj i).hom]
    [∀ i, QuasiSeparated (D.obj i).hom] [∀ {i j : I} (φ : i ⟶ j), IsAffineHom (D.map φ).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) {X' : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ c.pt.left} (sq : IsPullback g' f' f c.pt.hom)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : ∀ q, IsTorsionSheafOfInvertibleOrder S
      ((DerivedCategory.Plus.homologyFunctor _ q).obj E)) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app E) :=
  sorry

/-- Blueprint `lem-kun-0f1c`: Direct image commutes with base change along field extensions.

Let `L/K` be an extension of fields, let `g : T ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes over `K`, and let `g_L : T_L ⟶ S_L` be its base change to `Spec L`, given by
cartesian squares `S_L = S ×_K L` and `T_L = T ×_S S_L`. Then for every `E ∈ D⁺(T_ét, Λ)` whose
cohomology sheaves are torsion of orders invertible in `K`, the derived base change map
`π^* Rg_* E ⟶ Rg_{L,*} π'^* E` is an isomorphism: `Rg_{L,*} E_L` is the pullback of `Rg_* E`. -/
theorem Etale.isIso_baseChange_app_of_field {K L : Type u} [Field K] [Field L] [Algebra K L]
    {S T S' T' : Scheme.{u}} (s : S ⟶ Spec (.of K)) (g : T ⟶ S) [QuasiCompact g]
    [QuasiSeparated g] (π : S' ⟶ S) (s' : S' ⟶ Spec (.of L))
    (hS : IsPullback π s' s (Spec.map (CommRingCat.ofHom (algebraMap K L)))) (π' : T' ⟶ T)
    (g' : T' ⟶ S') (sq : IsPullback π' g' g π)
    (E : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : ∀ q, IsTorsionSheafOfInvertibleOrder (Spec (.of K))
      ((DerivedCategory.Plus.homologyFunctor _ q).obj E)) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app E) :=
  sorry

end AlgebraicGeometry
