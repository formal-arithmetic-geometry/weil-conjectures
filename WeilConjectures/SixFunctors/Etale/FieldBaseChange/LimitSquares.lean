/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Base change along limits of cartesian squares

Let `I` be cofiltered, `S = lim S_i` a limit of schemes over a fixed `S₀` with affine transition
morphisms, and `T = lim T_i` a compatible limit of schemes with qcqs morphisms `g_i : T_i ⟶ S_i`.
For a fixed `f₀ : X₀ ⟶ S₀` form the cartesian squares `X_i = X₀ ×_{S₀} S_i`,
`Y_i = X_i ×_{S_i} T_i` and their limit `X = X₀ ×_{S₀} S`, `Y = X ×_S T`. If the degree-`q`
base-change maps `p_i⁻¹ R^q g_{i,*} F_i ⟶ R^q h_{i,*} e_i⁻¹ F_i` are isomorphisms for a
compatible system of sheaves `F_i` (here: the pullbacks of a fixed sheaf `G`), so is the
base-change map of the limit square
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`).

This is the classical input `lem-kun-0ezt` of the blueprint, Stacks Project Tag 0EZT, for which
the blueprint records no proof. It is recorded here in the case of a system of sheaves pulled
back from a fixed scheme and of squares obtained by base change of a fixed `f₀`, which is the
case used in the proof of `lem-kun-0f1i`.

## References

- Stacks Project, Lemma 59.86.3, <https://stacks.math.columbia.edu/tag/0EZT>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0ezt`: higher direct images along limits of cartesian squares.

Let `I` be cofiltered, let `S_i` (`DS`) be a system of schemes over `S₀` and `T_i` (`DT`) a
system of schemes over `W`, both with affine transition morphisms and with limits `S` and `T`,
and let `g_i : T_i ⟶ S_i` and `g : T ⟶ S` be compatible quasi-compact quasi-separated
morphisms. For `f₀ : X₀ ⟶ S₀` let `X_i = X₀ ×_{S₀} S_i`, `Y_i = X_i ×_{S_i} T_i`, `X = X₀ ×_{S₀} S`
and `Y = X ×_S T`. If for a sheaf `G` of `Λ`-modules on `W` and a degree `q` every base-change
map `p_i⁻¹ R^q g_{i,*} (G|_{T_i}) ⟶ R^q h_{i,*} e_i⁻¹ (G|_{T_i})` is an isomorphism, then so is
`p⁻¹ R^q g_* (G|_T) ⟶ R^q h_* e⁻¹ (G|_T)`.

The blueprint states the lemma for a compatible system of torsion sheaves; here `Λ` is finite,
so every sheaf of `Λ`-modules is torsion, and the system is the one pulled back from `G`. -/
@[stacks 0EZT]
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit [Finite Λ]
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {S₀ X₀ W : Scheme.{u}} (f₀ : X₀ ⟶ S₀)
    (DS : I ⥤ Over S₀) [∀ {i j : I} (φ : i ⟶ j), IsAffineHom (DS.map φ).left]
    (cS : Cone DS) (_hcS : IsLimit ((Over.forget S₀).mapCone cS))
    (DT : I ⥤ Over W) [∀ {i j : I} (φ : i ⟶ j), IsAffineHom (DT.map φ).left]
    (cT : Cone DT) (_hcT : IsLimit ((Over.forget W).mapCone cT))
    (g : ∀ i, (DT.obj i).left ⟶ (DS.obj i).left)
    (_hg : ∀ {i j : I} (φ : i ⟶ j), (DT.map φ).left ≫ g j = g i ≫ (DS.map φ).left)
    (gL : cT.pt.left ⟶ cS.pt.left)
    (_hgL : ∀ i, (cT.π.app i).left ≫ g i = gL ≫ (cS.π.app i).left)
    [∀ i, QuasiCompact (g i)] [∀ i, QuasiSeparated (g i)] [QuasiCompact gL]
    [QuasiSeparated gL]
    {X Y : I → Scheme.{u}} (b : ∀ i, X i ⟶ X₀) (p : ∀ i, X i ⟶ (DS.obj i).left)
    (_hb : ∀ i, IsPullback (b i) (p i) f₀ (DS.obj i).hom)
    (e : ∀ i, Y i ⟶ (DT.obj i).left) (h : ∀ i, Y i ⟶ X i)
    (sq : ∀ i, IsPullback (e i) (h i) (g i) (p i))
    {XL YL : Scheme.{u}} (bL : XL ⟶ X₀) (pL : XL ⟶ cS.pt.left)
    (_hbL : IsPullback bL pL f₀ cS.pt.hom)
    (eL : YL ⟶ cT.pt.left) (hL : YL ⟶ XL) (sqL : IsPullback eL hL gL pL)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (_H : ∀ i, IsIso (Etale.baseChangeHomologyMap Λ (sq i) q
      (((DT.obj i).hom)^*[ModuleCat.{u + 1} Λ].obj G))) :
    IsIso (Etale.baseChangeHomologyMap Λ sqL q ((cT.pt.hom)^*[ModuleCat.{u + 1} Λ].obj G)) :=
  sorry

end AlgebraicGeometry
