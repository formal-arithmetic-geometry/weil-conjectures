/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.VaryingBase
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.Transport

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
    IsIso (Etale.baseChangeHomologyMap Λ sq₀ q (((w₀)^*[ModuleCat.{u + 1} Λ]).obj G)) := by
  have : ∀ i, QuasiCompact (h.app i) := fun i ↦
    MorphismProperty.of_isPullback (hsq i).flip inferInstance
  have : ∀ i, QuasiSeparated (h.app i) := fun i ↦
    MorphismProperty.of_isPullback (hsq i).flip inferInstance
  have : QuasiCompact h₀ := MorphismProperty.of_isPullback sq₀.flip inferInstance
  have : QuasiSeparated h₀ := MorphismProperty.of_isPullback sq₀.flip inferInstance
  let K := (DerivedCategory.Plus.singleFunctor (Sheaf W.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).obj G
  have hw' : ∀ i, cY.π.app i ≫ (e ≫ w).app i = e₀ ≫ w₀ := fun i ↦ by
    rw [NatTrans.comp_app, ← Category.assoc, ← he₀, Category.assoc, hw₀]
  let 𝒳 := Etale.varyingBaseSystem h hh₀ (e ≫ w) (e₀ ≫ w₀) hw'
  let 𝒜 := (Etale.varyingBaseSystem g hg₀ w w₀ hw₀).comapB p₀
  have h𝒳 := Etale.isStalkColimit_varyingBaseSystem Λ h hh₀ (e ≫ w) (e₀ ≫ w₀) hw' hX hY G q
  have h𝒜 := Etale.LimitStageSystem.isStalkColimit_comapB p₀ _
    (Etale.isStalkColimit_varyingBaseSystem Λ g hg₀ w w₀ hw₀ hS hT G q)
  let β (i : I) : Etale.LimitStage.Hom (𝒳.obj i) (𝒜.obj i) :=
    ⟨e.app i, p.app i, (hsq i).w, (hp₀ i).symm, rfl⟩
  let β₀ : Etale.LimitStage.Hom ⟨cY.pt, cX.pt, h₀, 𝟙 _, e₀ ≫ w₀⟩ 𝒜.pt :=
    ⟨e₀, p₀, sq₀.w, by simp [𝒜], rfl⟩
  have hβ (i : I) : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.LimitStage.transition Λ (β i)).app K)) :=
    Etale.LimitStage.isIso_homology_transition_of_isIso Λ (β i) q K
      ((Etale.isIso_baseChangeHomologyMap_iff_upperStar Λ (hsq i) q (w.app i) G).1 (H i))
  have hβ₀ : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.LimitStage.transition Λ β₀).app K)) := by
    refine Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ModuleCat.IsElementwiseColimit.bijective_of_bijective
      (fun i ↦ (Etale.stalkHomology Λ q x).map ((Etale.LimitStage.transition Λ (β i)).app K))
      ((Etale.stalkHomology Λ q x).map ((Etale.LimitStage.transition Λ β₀).app K))
      (fun i ↦ ?_) (fun f ↦ ?_) (fun f ↦ ?_) (fun i ↦ ?_) (h𝒜 x) (h𝒳 x)
    · have hc : (𝒳.π i).comp (β i) = β₀.comp (𝒜.π i) :=
        Etale.LimitStage.Hom.ext (he₀ i).symm (hp₀ i).symm
      rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
        Etale.LimitStage.transition_comp, Etale.LimitStage.transition_comp, hc]
    · have hc : (β _).comp (𝒜.map f) = (𝒳.map f).comp (β _) :=
        Etale.LimitStage.Hom.ext (e.naturality f).symm (p.naturality f).symm
      rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
        Etale.LimitStage.transition_comp, Etale.LimitStage.transition_comp, hc]
    · rw [← Functor.map_comp, ← NatTrans.comp_app, Etale.LimitStage.transition_comp, 𝒜.w]
    · exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  rw [Etale.isIso_baseChangeHomologyMap_iff_upperStar Λ sq₀ q w₀ G]
  exact Etale.LimitStage.isIso_homology_baseChange_of_isIso Λ β₀ q K hβ₀

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
