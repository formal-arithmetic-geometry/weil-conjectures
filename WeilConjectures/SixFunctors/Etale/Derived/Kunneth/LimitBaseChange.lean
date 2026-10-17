/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem

/-!
# Base change along limits of Cartesian squares

Let `I` be a cofiltered category and `i ↦ (Yᵢ, Xᵢ, Tᵢ, Sᵢ)` an inverse system of Cartesian
squares

```
Yᵢ --eᵢ--> Tᵢ
|          |
hᵢ         gᵢ
v          v
Xᵢ --pᵢ--> Sᵢ
```

with affine transition morphisms and `gᵢ` quasi-compact quasi-separated, with limit square
`(Y, X, T, S)`. If the degree-`q` base-change map
`pᵢ⁻¹ R^q gᵢ_* Fᵢ ⟶ R^q hᵢ_* eᵢ⁻¹ Fᵢ` is an isomorphism at every stage, then so is the one of
the limit square (blueprint `lem-kun-0ezt`, Stacks 0EZT). As an application, smooth base change
holds along limits of smooth schemes (blueprint `lem-kun-0f09`, Stacks 0F09).

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`: the limit statement for
  coefficients pulled back from a fixed scheme `W`.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_of_forall`: the limit
  statement when the stage maps are isomorphisms for all coefficient sheaves.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth`: smooth base change
  along a limit of smooth schemes.

## References

- Stacks Project, Lemma 59.88.3, <https://stacks.math.columbia.edu/tag/0EZT>
- Stacks Project, Lemma 59.89.3, <https://stacks.math.columbia.edu/tag/0F09>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0ezt`: Higher direct images along limits of cartesian squares.

Let `i ↦ (Yᵢ, Xᵢ, Tᵢ, Sᵢ)` be a cofiltered system of Cartesian squares
`IsPullback (e.app i) (h.app i) (g.app i) (p.app i)` with affine transition morphisms and every
`g.app i` quasi-compact quasi-separated, all `Sᵢ` and `Xᵢ` quasi-compact quasi-separated,
and let `sq₀ : IsPullback e₀ h₀ g₀ p₀` be a Cartesian
square of limits (the four limit cones being compatible with the four morphisms), with `g₀`
quasi-compact quasi-separated. Let `G` be a sheaf on a scheme `W` to which the system `T` maps.
If for a fixed degree `q` every base-change map `pᵢ⁻¹ R^q gᵢ_* (G|_{Tᵢ}) ⟶ R^q hᵢ_* eᵢ⁻¹ (G|_{Tᵢ})`
is an isomorphism, then so is `p₀⁻¹ R^q g₀_* (G|_T) ⟶ R^q h₀_* e₀⁻¹ (G|_T)`. -/
@[stacks 0EZT]
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {S X T Y : I ⥤ Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S) (e : Y ⟶ T)
    (h : Y ⟶ X) (hsq : ∀ i, IsPullback (e.app i) (h.app i) (g.app i) (p.app i))
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    [∀ i, CompactSpace (X.obj i)] [∀ i, QuasiSeparatedSpace (X.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (T.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f)]
    {cS : Cone S} (hS : IsLimit cS) {cX : Cone X} (hX : IsLimit cX)
    {cT : Cone T} (hT : IsLimit cT) {cY : Cone Y} (hY : IsLimit cY)
    {p₀ : cX.pt ⟶ cS.pt} {g₀ : cT.pt ⟶ cS.pt} {e₀ : cY.pt ⟶ cT.pt} {h₀ : cY.pt ⟶ cX.pt}
    (hp₀ : ∀ i, p₀ ≫ cS.π.app i = cX.π.app i ≫ p.app i)
    (hg₀ : ∀ i, g₀ ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (he₀ : ∀ i, e₀ ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (hh₀ : ∀ i, h₀ ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (sq₀ : IsPullback e₀ h₀ g₀ p₀) [QuasiCompact g₀] [QuasiSeparated g₀]
    {W : Scheme.{u}} (w : T ⟶ (Functor.const I).obj W) (w₀ : cT.pt ⟶ W)
    (hw₀ : ∀ i, cT.π.app i ≫ w.app i = w₀)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (H : ∀ i, IsIso (Etale.baseChangeHomologyMap Λ (hsq i) q
      (((w.app i)^*[ModuleCat.{u + 1} Λ]).obj G))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq₀ q (((w₀)^*[ModuleCat.{u + 1} Λ]).obj G)) :=
  sorry

/-- Blueprint `lem-kun-0ezt`: Higher direct images along limits of cartesian squares, for all
coefficient sheaves.

In the situation of `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`, if for a
fixed degree `q` every stage base-change map is an isomorphism for every sheaf of `Λ`-modules
on `Tᵢ`, then the base-change map of the limit square is an isomorphism for every sheaf `F` of
`Λ`-modules on `T`: such an `F` is the filtered colimit of the pullbacks of its direct images to the stages (blueprint
`lem-kun-descent-limit`). -/
@[stacks 0EZT]
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_of_forall {I : Type u} [Category.{u} I]
    [IsCofiltered I] {S X T Y : I ⥤ Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S) (e : Y ⟶ T)
    (h : Y ⟶ X) (hsq : ∀ i, IsPullback (e.app i) (h.app i) (g.app i) (p.app i))
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    [∀ i, CompactSpace (X.obj i)] [∀ i, QuasiSeparatedSpace (X.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (T.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f)]
    {cS : Cone S} (hS : IsLimit cS) {cX : Cone X} (hX : IsLimit cX)
    {cT : Cone T} (hT : IsLimit cT) {cY : Cone Y} (hY : IsLimit cY)
    {p₀ : cX.pt ⟶ cS.pt} {g₀ : cT.pt ⟶ cS.pt} {e₀ : cY.pt ⟶ cT.pt} {h₀ : cY.pt ⟶ cX.pt}
    (hp₀ : ∀ i, p₀ ≫ cS.π.app i = cX.π.app i ≫ p.app i)
    (hg₀ : ∀ i, g₀ ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (he₀ : ∀ i, e₀ ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (hh₀ : ∀ i, h₀ ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (sq₀ : IsPullback e₀ h₀ g₀ p₀) [QuasiCompact g₀] [QuasiSeparated g₀] (q : ℤ)
    (H : ∀ i (F : Sheaf (T.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso (Etale.baseChangeHomologyMap Λ (hsq i) q F))
    (F : Sheaf cT.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq₀ q F) :=
  sorry

/-- Blueprint `lem-kun-0f09`: Smooth base change for limits of smooth schemes.

Let `S' = lim Sᵢ` be a cofiltered limit of schemes `Sᵢ` which are smooth, quasi-compact and
quasi-separated over `S`, with affine transition morphisms, let `g : T ⟶ S` be quasi-compact
quasi-separated and form the Cartesian square

```
Y --e--> T
|        |
h        g
v        v
S' -----> S
```

Then for every sheaf `F` of `Λ`-modules on `T` whose geometric stalks are torsion of orders
invertible on `S`, the base-change map `R^q g_* F |_{S'} ⟶ R^q h_* e⁻¹ F` is an isomorphism in
every degree `q`. -/
@[stacks 0F09]
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth {S T : Scheme.{u}} (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over S) [∀ i, Smooth (D.obj i).hom] [∀ i, QuasiCompact (D.obj i).hom]
    [∀ i, QuasiSeparated (D.obj i).hom] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) {Y : Scheme.{u}} {e : Y ⟶ T}
    {h : Y ⟶ c.pt.left} (sq : IsPullback e h g c.pt.hom) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

end AlgebraicGeometry
