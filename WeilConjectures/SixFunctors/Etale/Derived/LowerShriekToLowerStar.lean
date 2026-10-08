/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# The derived comparison from extension by zero to pushforward

For an open immersion `j` the derived extension by zero `D(j_!)` maps to the derived
pushforward `Rj_*`; composing with the proper pushforward of a compactification `(i, g)` of
`f` gives the *forget-supports* map

`Rf_! = Rg_* D(i_!) ⟶ Rg_* Ri_*`,

whose target is right adjoint to `Li^* Lg^*`. For a proper `f` the open immersion `i` is also a
closed immersion (`AlgebraicGeometry.Compactification.isClosedImmersion_openImmersion`), the
comparison `D(i_!) ⟶ Ri_*` of a clopen immersion is an isomorphism, and hence so is the
forget-supports map. Composed with `Ri_* ⋙ Rg_* ≅ R(i ≫ g)_* = Rf_*` it identifies `Rf_!` with
`Rf_*`. In that case a class `K ⟶ Rf_! N` is transposed into a morphism `Lf^* K ⟶ N` by the
adjunction `Lf^* ⊣ Rf_*`.

The comparison for an open immersion is the transpose, under `D(j^*) ⊣ Rj_*`, of the inverse
of the unit `K ⟶ D(j^*) D(j_!) K`, which is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit`).

## Main definitions

- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekToLowerStar`
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekToLowerStarComp`
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`: `Rf_! ≅ Rf_*` for
  a proper `f`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekTranspose`
- `AlgebraicGeometry.Etale.leftDerivedUpperStarId`,
  `AlgebraicGeometry.Etale.rightDerivedLowerStarId` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekId`: the derived functors of the identity
  morphism are the identity.

## Main statements

- `AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar`: `D(j_!) ⟶ Rj_*` is
  an isomorphism for an immersion `j` that is both open and closed.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper`: the
  forget-supports map is an isomorphism for a proper `f`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived comparison `D(j_!) ⟶ Rj_*` along an open immersion `j`: the transpose, under
`D(j^*) ⊣ Rj_*`, of the inverse of the unit `K ⟶ D(j^*) D(j_!) K` of `D(j_!) ⊣ D(j^*)`. It is
the derived counterpart of the comparison `j_! ⟶ j_*` of sheaves. Componentwise it is the
composite

```
          η_{D(j_!) K}                         Rj_* (η'_K)⁻¹
D(j_!) K ─────────────▶ Rj_* D(j^*) D(j_!) K ───────────────▶ Rj_* K
```

of the unit `η` of `D(j^*) ⊣ Rj_*` and the inverse of the unit `η'` of `D(j_!) ⊣ D(j^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekToLowerStar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : D((j)_!open[A]) ⟶ R((j)_*[A]) :=
  Functor.whiskerLeft D((j)_!open[A]) (mapDerivedUpperStarLowerStarAdjunction A j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (inv (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit)
        R((j)_*[A])

/-- For an immersion `j` that is both open and closed, the derived comparison
`D(j_!) ⟶ Rj_*` is an isomorphism. -/
instance isIso_derivedOpenImmersionLowerShriekToLowerStar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekToLowerStar A j) :=
  -- Proof sketch: since the range of `j` is clopen, the sheaf-level comparison `j_! ⟶ j_*` is
  -- an isomorphism (both are extension by zero across the complementary open), and `j_*` is
  -- exact. So `Rj_* ≅ D(j_*) ≅ D(j_!)`, compatibly with the comparison.
  sorry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The *forget-supports* map `Rf_! ⟶ Ri_* ⋙ Rg_*` for the chosen compactification `(i, g)` of
`f`: the proper pushforward `Rg_*` applied to the comparison `D(i_!) ⟶ Ri_*` of the open
immersion `i`. Its target is right adjoint to `Lg^* ⋙ Li^*`. -/
noncomputable def rightDerivedLowerShriekToLowerStarComp :
    R(f)_![A] ⟶ R(((HasCompactification.compactification f).i)_*[A]) ⋙
      R(((HasCompactification.compactification f).g)_*[A]) :=
  Functor.whiskerRight (derivedOpenImmersionLowerShriekToLowerStar A _) _

/-- For a proper `f`, the open immersion `i` of the chosen compactification is also a closed
immersion. -/
instance isClosedImmersion_compactification_i [IsProper f] :
    IsClosedImmersion (HasCompactification.compactification f).i :=
  (HasCompactification.compactification f).isClosedImmersion_openImmersion ‹_›

/-- For a proper morphism `f`, the forget-supports map `Rf_! ⟶ Ri_* ⋙ Rg_*` of the chosen
compactification `(i, g)` is an isomorphism:
```
      i          g
  X ─────▶ X̄ ─────▶ Y        f = i ≫ g,  i open immersion,  g proper
  └──────────────────▶
           f

  Rf_! = D(i_!) ⋙ Rg_* ──(D(i_!) ⟶ Ri_*) ▷ Rg_*──▶ Ri_* ⋙ Rg_*
```
Since `f` is proper, `i` is also a closed immersion
(`AlgebraicGeometry.Etale.isClosedImmersion_compactification_i`), so the comparison
`D(i_!) ⟶ Ri_*` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar`). -/
instance isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper [IsProper f] :
    IsIso (rightDerivedLowerShriekToLowerStarComp A f) := by
  have := isIso_derivedOpenImmersionLowerShriekToLowerStar A
    (HasCompactification.compactification f).i
  exact Functor.isIso_whiskerRight _ _

/-- For a proper morphism `f`, compactly supported and ordinary direct image agree,
`Rf_! ≅ Rf_*`: the forget-supports map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekToLowerStarComp`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper`, followed
by `Ri_* ⋙ Rg_* ≅ R(i ≫ g)_* = Rf_*`:
```
          forget supports                rightDerivedLowerStarComp
   Rf_! ─────────────────▶ Ri_* ⋙ Rg_* ─────────────────────────▶ R(i ≫ g)_* ═══ Rf_*
```
-/
noncomputable def rightDerivedLowerShriekIsoRightDerivedLowerStar [IsProper f] :
    R(f)_![A] ≅ R((f)_*[A]) :=
  asIso (rightDerivedLowerShriekToLowerStarComp A f) ≪≫
    rightDerivedLowerStarComp A _ _ ≪≫
      rightDerivedLowerStarCongr A (HasCompactification.compactification f).comm.symm

lemma rightDerivedLowerShriekIsoRightDerivedLowerStar_hom [IsProper f] :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom =
      rightDerivedLowerShriekToLowerStarComp A f ≫ (rightDerivedLowerStarComp A _ _).hom ≫
        (rightDerivedLowerStarCongr A (HasCompactification.compactification f).comm.symm).hom :=
  rfl

/-- The *transpose* of a class `γ : K ⟶ Rf_! N` along the forget-supports map: the morphism
`Li^* Lg^* K ⟶ N` adjoint, under `Li^* Lg^* ⊣ Rg_* Ri_*`, to
`K ⟶ Rf_! N ⟶ Rg_* Ri_* N`, where `(i, g)` is the chosen compactification of `f`.

For a proper `f` the forget-supports map is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper`)
and this is the adjunction `Lf^* ⊣ Rf_*`, transported along `Rf_! ≅ Rf_*`. -/
noncomputable def rightDerivedLowerShriekTranspose
    {K : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {N : DerivedCategory (Sheaf X.smallEtaleTopology A)} (γ : K ⟶ (R(f)_![A]).obj N) :
    (L(((HasCompactification.compactification f).i)^*[A])).obj
        ((L(((HasCompactification.compactification f).g)^*[A])).obj K) ⟶ N :=
  (((derivedUpperStarLowerStarAdjunction A _).comp
    (derivedUpperStarLowerStarAdjunction A _)).homEquiv _ _).symm
      (γ ≫ (rightDerivedLowerShriekToLowerStarComp A f).app N)

/-- The derived pullback along the identity is the identity, `L(𝟙 X)^* ≅ 𝟭`: the derived
functor of `Etale.upperStarId`, followed by `L(𝟭) ≅ D(𝟭) ≅ 𝟭`. -/
noncomputable def leftDerivedUpperStarId (X : Scheme.{u}) : L((𝟙 X)^*[A]) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId A X) ≪≫
    (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The derived pushforward along the identity is the identity, `R(𝟙 X)_* ≅ 𝟭`: both are right
adjoint to `L(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def rightDerivedLowerStarId (X : Scheme.{u}) : R(((𝟙 X))_*[A]) ≅ 𝟭 _ :=
  ((derivedUpperStarLowerStarAdjunction A (𝟙 X)).ofNatIsoLeft
    (leftDerivedUpperStarId A X)).rightAdjointUniq Adjunction.id

/-- The compactly supported direct image along the identity is the identity,
`R(𝟙 X)_! ≅ R(𝟙 X)_* ≅ 𝟭`, the identity being proper. -/
noncomputable def rightDerivedLowerShriekId (X : Scheme.{u}) : R(𝟙 X)_![A] ≅ 𝟭 _ :=
  rightDerivedLowerShriekIsoRightDerivedLowerStar A (𝟙 X) ≪≫ rightDerivedLowerStarId A X

/-- The compactly supported direct image along an endomorphism equal to the identity is the
identity. This is `AlgebraicGeometry.Etale.rightDerivedLowerShriekId` transported along
`f = 𝟙 X`, for an `f` such as `s ≫ p` with `s` a section of `p`. -/
theorem nonempty_iso_rightDerivedLowerShriek_of_eq_id {X : Scheme.{u}} (f : X ⟶ X)
    [HasCompactification f] (hf : f = 𝟙 X) : Nonempty (R(f)_![A] ≅ 𝟭 _) := by
  subst hf
  exact ⟨rightDerivedLowerShriekId A X⟩

end Etale

end AlgebraicGeometry
