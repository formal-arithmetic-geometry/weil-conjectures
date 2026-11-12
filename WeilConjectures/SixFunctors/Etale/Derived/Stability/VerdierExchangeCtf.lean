/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.CtfStability
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage

/-!
# The Verdier exchange formulas obtained by biduality

For a finite coefficient ring `Λ` whose exponent is invertible on an algebraically closed field
`k` and a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, this file derives from
the exchange isomorphisms `𝔻_Y Rf_! ≅ Rf_* 𝔻_X` and `Rf^! 𝔻_Y ≅ 𝔻_X f^*` and from Verdier
biduality on `Dctf` the exchange isomorphisms of the right column of blueprint
`corollary-verdier-exchange-formulas`:

- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedUpperShriek`
  (`corollary-verdier-exchange-formulas--4`): `𝔻_X Rf^! L ≅ f^* 𝔻_Y L` for `L ∈ Dctf(Y, Λ)`;
- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerStar`
  (`corollary-verdier-exchange-formulas--2`): `𝔻_Y Rf_* K ≅ Rf_! 𝔻_X K` for `K ∈ Dctf(X, Λ)`;
- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerStar_of_isOpenImmersion`
  (`corollary-verdier-exchange-formulas--6`): `𝔻_X Rj_* K ≅ j_! 𝔻_U K` for an open immersion `j`
  and `K ∈ Dctf(U, Λ)`, `j_!` being extension by zero.

As in `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality`, the isomorphisms are stated
as the existence of an isomorphism for each object.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `corollary-verdier-exchange-formulas--4`: the dual of the exceptional inverse
image. For a morphism `f : X ⟶ Y` over `k` of separated `k`-schemes of finite type and
`L ∈ Dctf(Y, Λ)`, `𝔻_X (Rf^! L) ≅ Lf^* (𝔻_Y L)`. It is `Rf^! L ≅ 𝔻_X f^* 𝔻_Y L`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar`)
dualized on `X`, with biduality for `f^* 𝔻_Y L ∈ Dctf(X, Λ)`. -/
theorem nonempty_iso_verdierDual_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aX] [HasCompactification aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] [HasCompactification aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasCompactification f]
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty ((verdierDual Λ aX).obj (op ((R(f)^![Λ]).obj L)) ≅
      (L((f)^*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ aY).obj (op L))) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY f
    hf hL
  obtain ⟨b⟩ := nonempty_iso_verdierDual_verdierDual Λ aX
    (constructibleFiniteTor_leftDerivedUpperStar _ f (constructibleFiniteTor_verdierDual Λ aY hL))
  exact ⟨(verdierDual Λ aX).mapIso e.op.symm ≪≫ b.symm⟩

/-- Blueprint `corollary-verdier-exchange-formulas--2`: the dual of the ordinary direct image.
For a morphism `f : X ⟶ Y` over `k` of separated `k`-schemes of finite type and
`K ∈ Dctf(X, Λ)`, `𝔻_Y (Rf_* K) ≅ Rf_! (𝔻_X K)`. It is the exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`
(`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek`) at `𝔻_X K`, with
biduality on `X` and on `Y`. -/
theorem nonempty_iso_verdierDual_rightDerivedLowerStar {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aX] [HasCompactification aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] [HasCompactification aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasCompactification f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty ((verdierDual Λ aY).obj (op ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).obj ((verdierDual Λ aX).obj (op K))) := by
  subst hf
  have : HasInvertibleExponent Λ Y := .of_hom aY
  have : QuasiCompact f := by
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : IsNoetherian Y := {}
    exact QuasiCompact.of_comp f aY
  have hN := constructibleFiniteTor_rightDerivedLowerShriek Λ aY f
    (constructibleFiniteTor_verdierDual Λ (f ≫ aY) hK)
  obtain ⟨e⟩ := nonempty_iso_verdierDual_rightDerivedLowerShriek Λ f aY
    ((verdierDual Λ (f ≫ aY)).obj (op K))
  obtain ⟨bX⟩ := nonempty_iso_verdierDual_verdierDual Λ (f ≫ aY) hK
  obtain ⟨bY⟩ := nonempty_iso_verdierDual_verdierDual Λ aY hN
  let i := e ≪≫ (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso bX.symm
  exact ⟨(verdierDual Λ aY).mapIso i.op ≪≫ bY.symm⟩

/-- Blueprint `corollary-verdier-exchange-formulas--6`: the dual of the direct image along an
open immersion. For an open immersion `j : U ⟶ X` of separated `k`-schemes of finite type and
`K ∈ Dctf(U, Λ)`, `𝔻_X (Rj_* K) ≅ j_! (𝔻_U K)`, where `j_!` is extension by zero. It is
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerStar` for `f = j`, with
`Rj_! ≅ j_!` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion`). -/
theorem nonempty_iso_verdierDual_rightDerivedLowerStar_of_isOpenImmersion {U X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    [HasCompactification aX] (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j]
    [HasCompactification (j ≫ aX)]
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) U K) :
    Nonempty ((verdierDual Λ aX).obj (op ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      D((j)_!open[ModuleCat.{u + 1} Λ]).obj ((verdierDual Λ (j ≫ aX)).obj (op K))) := by
  have : QuasiCompact j := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
    have : IsNoetherian X := {}
    infer_instance
  obtain ⟨e⟩ := nonempty_iso_verdierDual_rightDerivedLowerStar Λ (j ≫ aX) aX j rfl hK
  exact ⟨e ≪≫ (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).app _⟩

end Etale

end AlgebraicGeometry
