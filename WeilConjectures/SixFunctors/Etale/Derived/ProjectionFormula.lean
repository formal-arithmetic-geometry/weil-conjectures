/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap.Comp
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!

# The projection formula for compactly supported direct image

Let `A` be a monoidal Grothendieck abelian coefficient category and let `f : X ⟶ Y` be a
morphism of schemes admitting a compactification, so that the compactly supported direct
image `Rf_! : D(X_ét) ⥤ D(Y_ét)` is available. The *projection formula* is the assertion
that the projection map

```
  PF_{f, K, L} : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

of `AlgebraicGeometry.Etale.projectionMapOfCompactification` is an isomorphism, for
`K : D(X_ét)` and `L : D(Y_ét)`.

## Main definitions

- `AlgebraicGeometry.Etale.HasProjectionFormulaOfCompactification` : the projection formula
  for `Rf_!` computed with a given compactification `c` of `f`.
- `AlgebraicGeometry.Etale.HasProjectionFormula` : the projection formula for `Rf_!`
  computed with the chosen compactification `HasCompactification.compactification f`.

## Main statements

- `AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral`
  (`sk-thm-sf-pf-adic`) : the projection formula at the integral stage `𝒪_E`, for derived
  complete objects of finite Tor amplitude.
- `AlgebraicGeometry.Etale.hasProjectionFormula_field` (`sk-thm-sf-pf-field`) : the
  projection formula over a field of coefficients, at a dualizable object.
- `AlgebraicGeometry.Etale.isIso_projectionMap_of_finite` : the projection formula at a finite
  coefficient ring, on the whole unbounded derived categories, as an isomorphism of bifunctors.
- `AlgebraicGeometry.Etale.hasProjectionFormula_of_finite` : its objectwise form, a
  strengthening of `sk-thm-sf-pf-finite`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight`,
  `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek` : where the
  projection formula holds, the projection map is a natural isomorphism in either variable.
- `AlgebraicGeometry.Etale.hasProjectionFormula_id`,
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp` (in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComp`),
  `AlgebraicGeometry.Etale.hasProjectionFormula_comp`,
  `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_iff`
  (`sk-prop-sf-pf-coherence`) : the coherence of the projection formula.

## Implementation notes

The projection map `PF_{f, K, L}` is
`AlgebraicGeometry.Etale.projectionMapOfCompactification`, built in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection` from a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`: it is the projection map of `Rg_*` followed by the inverse of
the projection formula for the open immersion `i`. The projection formula is the assertion
`IsIso (PF_{f, K, L})`. Building `PF` needs `Etale.UpperStarPreservesFlat A` and a concrete
structure on `A` (with `forget A` reflecting isomorphisms, preserving filtered colimits and
sheaves); these hold for `A = ModuleCat Λ`.

The statements of `sk-prop-sf-pf-coherence` below are still objectwise: the identity case,
the composition law and the independence of the compactification. The blueprint node also
asks for identities between natural transformations — naturality in `f`, the associativity
pentagon, agreement with the direct-image projection formula for proper `f` through
`Rf_! ≅ Rf_*`, and compatibility with finite reduction, scalar extension and the pro-étale
realization. These need comparison isomorphisms for `Rf_!` (composition, change of
compactification) that are not constructed yet, and are not stated.

The integral stage is modelled exactly as in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient`: the
coefficient category is `ModuleCat 𝒪_E` for `𝒪_E = PadicAlgCl.integers l E` the ring of
integers of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` (transported to the universe `u + 1` by
`Shrink`), and derived completeness is `DerivedCategory.derivedCompleteIntegral`, that is,
derived completeness for the maximal ideal `𝔪_E`.

`AlgebraicGeometry.Etale.hasProjectionFormula_field` is stated for an arbitrary field of
coefficients and a dualizable second argument. The blueprint proves the two instances it needs,
`F = E` and `F = ℚ̄_ℓ`, for constructible objects, by rationalizing the integral statement and
passing to the `2`-colimit over the finite stages; on the étale site with discrete coefficients
the projection formula fails for constructible objects over a field of characteristic zero, the
skyscraper sheaves reducing it to proper base change (see the docstring of
`AlgebraicGeometry.Etale.hasProjectionFormula_field`).

-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Defs

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}}

/-- The projection formula for a morphism `f : X ⟶ Y`, at `K : D(X_ét)` and `L : D(Y_ét)`,
with `Rf_!` computed from a chosen compactification `c` of `f`: the assertion that the
projection map

```
  PF_c : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

of `AlgebraicGeometry.Etale.projectionMapOfCompactification` is an isomorphism. -/
def HasProjectionFormulaOfCompactification {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
  IsIso (((projectionMapOfCompactification A c).app K).app L)

/-- The projection formula for a morphism `f : X ⟶ Y` admitting a compactification, at
`K : D(X_ét)` and `L : D(Y_ét)`: the assertion that the projection map

```
  PF : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

of `AlgebraicGeometry.Etale.projectionMap` is an isomorphism, with `Rf_!` the compactly
supported direct image `AlgebraicGeometry.Etale.rightDerivedLowerShriek` attached to the
chosen compactification of `f`. -/
def HasProjectionFormula (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
  HasProjectionFormulaOfCompactification A (HasCompactification.compactification f) K L

omit [HasSmallSiteSheafify A] in
/-- If the projection formula holds for `f` at every `K` and a fixed `L`, the projection map is
a natural isomorphism `Rf_!(-) ⊗ᴸ L ≅ Rf_!(- ⊗ᴸ Lf^* L)` of functors `D(X_ét) ⥤ D(Y_ét)`. -/
theorem nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight (f : X ⟶ Y)
    [HasCompactification f] (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h : ∀ K, HasProjectionFormula A f K L) :
    Nonempty (R(f)_![A] ⋙ derivedTensorRight A Y L ≅
      derivedTensorRight A X ((L((f)^*[A])).obj L) ⋙ R(f)_![A]) :=
  have : ∀ K, IsIso ((((flipFunctor _ _ _).map (projectionMap A f)).app L).app K) := h
  have := NatIso.isIso_of_isIso_app (((flipFunctor _ _ _).map (projectionMap A f)).app L)
  ⟨asIso (((flipFunctor _ _ _).map (projectionMap A f)).app L)⟩

omit [HasSmallSiteSheafify A] in
/-- If the projection formula holds for `f` at a fixed `K` and every `L`, the projection map is
a natural isomorphism `Rf_! K ⊗ᴸ - ≅ Rf_!(K ⊗ᴸ Lf^*(-))` of functors `D(Y_ét) ⥤ D(Y_ét)`. -/
theorem nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek (f : X ⟶ Y)
    [HasCompactification f] (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h : ∀ L, HasProjectionFormula A f K L) :
    Nonempty ((derivedTensor A Y).obj ((R(f)_![A]).obj K) ≅
      L((f)^*[A]) ⋙ (derivedTensor A X).obj K ⋙ R(f)_![A]) :=
  have : ∀ L, IsIso (((projectionMap A f).app K).app L) := h
  have := NatIso.isIso_of_isIso_app ((projectionMap A f).app K)
  ⟨asIso ((projectionMap A f).app K)⟩

end Defs

section Integral

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-sf-pf-adic`: Projection formula: the derived-complete stage.

At the integral stage of the `ℓ`-adic formalism, where the coefficients are the ring of
integers `𝒪_E` of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`: if `K` and `L` are bounded
constructible, derived complete for the maximal ideal `𝔪_E` and of finite Tor amplitude, then
the projection formula holds for `f` at `K` and `L`. Constructibility is needed: the proof
checks the projection map modulo `𝔪_E`, where it is the finite-stage projection formula, and
concludes by conservativity of the reduction on derived complete objects, which needs both
sides derived complete; `Rf_! K ⊗ᴸ L` is derived complete for constructible `K` and `L`, but not
in general. -/
theorem hasProjectionFormula_of_derivedCompleteIntegral (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hKc : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) X K)
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (hKt : DerivedCategory.finiteTorAmplitude
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) X K)
    (hLc : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) Y L)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (hLt : DerivedCategory.finiteTorAmplitude
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) Y L) :
    HasProjectionFormula
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) f K L :=
  sorry

end Integral

section Field

variable (F : Type (u + 1)) [Field F]

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-sf-pf-field`: Projection formula: rational and algebraically closed
stages.

Over a field `F` of coefficients — the blueprint names the two instances `F = E`, the
rational stage, and `F = ℚ̄_ℓ`, the algebraically closed stage — the projection formula
holds for `f` at any `K` and any dualizable `L`, that is, a lisse `L` (for instance a
bounded complex with locally constant cohomology sheaves of finite rank).

On the étale site with the discrete field `F` as coefficients, the projection formula does not
hold for every bounded constructible `L`. For `L = y_* F` the skyscraper at the closed point
`y` of the spectrum `Y` of a strictly henselian discrete valuation ring, `f : X ⟶ Y` a regular
proper curve with nodal special fibre `X_y` and `K = F_X`, the projection map is the restriction
`RΓ(X, F) ⟶ RΓ(X_y, F)`; for `F` of characteristic zero, `H¹(X, F) = 0` since `X` is normal,
while `H¹(X_y, F) = F`. The blueprint reaches the constructible objects at the stages `E` and
`ℚ̄_ℓ` through the `ℓ`-adic formalism instead. For dualizable `L` the projection formula is formal:
it holds for the open immersion of a compactification, and for its proper part `g` the
projection map of `Rg_*` is the mate of the monoidal structure of `Lg^*`, invertible at a
dualizable object. -/
theorem hasProjectionFormula_field (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} F)))
    (hL : IsDualizable L) :
    HasProjectionFormula (ModuleCat.{u + 1} F) f K L :=
  sorry

end Field

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

/-- **The projection formula for a proper direct image at finite coefficients, unbounded.**
For a finite coefficient ring `Λ` and a proper morphism `g : Z ⟶ Y`, the projection map

`Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)`

of `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap` is an isomorphism of bifunctors
on the unbounded derived categories.

This is the non-formal part of the unbounded projection formula
`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`, the part for the open immersion of a
compactification being formal. It holds by SGA 4 XVII 5.2.9: the question is local on `Y`,
over a quasi-compact open the fibres of `g` have bounded dimension, so `Rg_*` has finite
cohomological dimension on torsion sheaves and commutes with direct sums; on geometric stalks,
by unbounded proper base change, it becomes `RΓ(Z_ȳ, M) ⊗ᴸ N ≅ RΓ(Z_ȳ, M ⊗ᴸ N)` for a complex
`N` of `Λ`-modules, which holds for `N = Λ` and passes to all `N` through these colimits. -/
theorem isIso_rightDerivedLowerStarProjectionMap_of_finite [Finite Λ] {Z : Scheme.{u}}
    (g : Z ⟶ Y) [IsProper g] :
    IsIso (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g) :=
  sorry

/-- **The projection formula at finite coefficients, unbounded.** For a finite coefficient
ring `Λ` and `f : X ⟶ Y` admitting a compactification, the projection map

`PF : Rf_! K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)`

of `AlgebraicGeometry.Etale.projectionMap` is an isomorphism of bifunctors on the whole
unbounded derived categories, with no boundedness, constructibility or Tor amplitude hypothesis
on `K` and `L`.

This is an unbounded form of clause (5) of `prop-functor-package`, from which the case
`sk-thm-sf-pf-finite` (`AlgebraicGeometry.Etale.hasProjectionFormula_of_boundedConstructible`)
is read off.

For the compactification `c = (X ⟶[i] Z ⟶[g] Y)` the projection map is the projection map of
`Rg_*` followed by isomorphisms (`AlgebraicGeometry.Etale.projectionMapOfCompactification_app_app`),
the projection formula for the open immersion `i` being formal
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`). So this is the proper
case `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`. -/
theorem isIso_projectionMap_of_finite [Finite Λ] (f : X ⟶ Y) [HasCompactification f] :
    IsIso (projectionMap (ModuleCat.{u + 1} Λ) f) :=
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ
    (HasCompactification.compactification f).g
  have (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app K) :=
    have (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
        IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L) := by
      rw [projectionMap, projectionMapOfCompactification_app_app]
      infer_instance
    NatIso.isIso_of_isIso_app _
  NatIso.isIso_of_isIso_app _

/-- The projection formula at finite coefficients, objectwise: for a finite coefficient ring
`Λ`, the projection formula holds for `f` at all `K` and `L`.

This is a strengthening of the blueprint node `sk-thm-sf-pf-finite`, which asks for `K`
bounded constructible, `L` of finite Tor amplitude and `Λ = A_{E,n}`. It is read off from
`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`. -/
theorem hasProjectionFormula_of_finite [Finite Λ] (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HasProjectionFormula (ModuleCat.{u + 1} Λ) f K L := by
  have := isIso_projectionMap_of_finite Λ f
  exact inferInstanceAs (IsIso (((projectionMap _ f).app K).app L))

end Finite

section Coherence

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y Z : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
include FC CC in
/-- The projection formula for a compactification `c = (X ⟶[i] Z ⟶[g] Y)` holds at `(K, L)` as
soon as the projection map of `Rg_*` is an isomorphism at `(i_!K, L)`, the open part of the
projection map being an isomorphism. -/
lemma hasProjectionFormulaOfCompactification_of_isIso {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h : IsIso (((rightDerivedLowerStarProjectionMap A c.g).app (D((c.i)_!open[A]).obj K)).app L)) :
    HasProjectionFormulaOfCompactification A c K L := by
  rw [HasProjectionFormulaOfCompactification, projectionMapOfCompactification_app_app]
  infer_instance

include FC CC in
/-- **The projection map of `Rg_*` at an extension by zero from an open and closed section.**
Let `i : X ⟶ Z` be an open and closed immersion with `i ≫ g = 𝟙 X`. Then the projection map
`Rg_*(i_!K) ⊗ᴸ L ⟶ Rg_*(i_!K ⊗ᴸ Lg^*L)` is an isomorphism.

It is checked through the second adjunction `Li^* ⊣ Ri_*`
(`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_of_comp`): the composite
left adjoint `Li^* Lg^* ≅ L(i ≫ g)^* = L(𝟙 X)^*` is an equivalence, `Ri_*` is fully faithful
as `i` is an open immersion, and `i_!K ≅ Ri_*K` and `i_!K ⊗ᴸ Lg^*L ≅ i_!(K ⊗ᴸ Li^*Lg^*L)`
lie in the essential image of `Ri_*`, `i` being also closed. No monoidal coherence of the
comparison `Lg^*(- ⊗ᴸ -) ≅ Lg^* - ⊗ᴸ Lg^* -` is needed. -/
lemma isIso_rightDerivedLowerStarProjectionMap_app_app_of_section {X Z : Scheme.{u}}
    (i : X ⟶ Z) (g : Z ⟶ X) [IsOpenImmersion i] [IsClosedImmersion i] (hig : i ≫ g = 𝟙 X)
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (((rightDerivedLowerStarProjectionMap A g).app (D((i)_!open[A]).obj K)).app L) := by
  let adj := derivedUpperStarLowerStarAdjunction A g
  let adj' := derivedUpperStarLowerStarAdjunction A i
  -- the composite left adjoint `Lg^* ⋙ Li^*` is an equivalence
  let e : L((g)^*[A]) ⋙ L((i)^*[A]) ≅ 𝟭 _ :=
    (leftDerivedUpperStarComp A i g (𝟙 X) hig.symm).symm ≪≫
      leftDerivedUpperStarIsoMapDerivedCategory A (𝟙 X) ≪≫
      Functor.mapDerivedCategoryNatIso (upperStarId A X) ≪≫ Functor.mapDerivedCategoryIdIso _
  have : (L((g)^*[A]) ⋙ L((i)^*[A])).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  -- `Ri_*` is fully faithful
  have : IsIso (mapDerivedUpperStarLowerStarAdjunction A i).counit :=
    (Adjunction.Triple.mk (derivedOpenImmersionLowerShriekUpperStarAdjunction A i)
      (mapDerivedUpperStarLowerStarAdjunction A i)).isIso_unit_iff_isIso_counit.1
        inferInstance
  have : R((i)_*[A]).Full :=
    (mapDerivedUpperStarLowerStarAdjunction A i).fullyFaithfulROfIsIsoCounit.full
  have : R((i)_*[A]).Faithful :=
    (mapDerivedUpperStarLowerStarAdjunction A i).fullyFaithfulROfIsIsoCounit.faithful
  -- `Li^*` of the counit of `Lg^* ⊣ Rg_*` at `i_!K` is an isomorphism
  let M := D((i)_!open[A]).obj K
  let eM : M ≅ R((i)_*[A]).obj K :=
    asIso ((derivedOpenImmersionLowerShriekToLowerStar A i).app K)
  have hε : IsIso (L((i)^*[A]).map (adj.counit.app M)) := by
    have h₁ : IsIso (L((i)^*[A]).map (adj.counit.app (R((i)_*[A]).obj K))) := by
      have h₀ : IsIso ((adj.comp adj').counit.app K) := inferInstance
      rw [Adjunction.comp_counit_app] at h₀
      exact IsIso.of_isIso_comp_right _ (adj'.counit.app K)
    have h₂ := adj.counit.naturality eM.hom
    dsimp at h₂
    rw [← cancel_mono eM.inv, Category.assoc, Category.assoc, eM.hom_inv_id,
      Category.comp_id] at h₂
    rw [← h₂]
    simp only [Functor.map_comp]
    infer_instance
  have hT : IsIso (L((i)^*[A]).map (((-⊗ᴸ-(Z)[A]).map (adj.counit.app M)).app
      ((L((g)^*[A])).obj L))) := by
    let ψ := leftDerivedUpperStarTensorNatIso A i
    let b := (L((g)^*[A])).obj L
    let ψb : (leftDerivedUpperStarDerivedTensor A i).flip.obj b ≅
        (derivedTensorLeftDerivedUpperStar A i).flip.obj b :=
      NatIso.ofComponents (fun a ↦ (ψ.app a).app b)
        (fun f ↦ NatTrans.congr_app (ψ.hom.naturality f) b)
    exact (NatIso.isIso_map_iff ψb (adj.counit.app M)).2
      (inferInstanceAs (IsIso (((-⊗ᴸ-(X)[A]).map (L((i)^*[A]).map (adj.counit.app M))).app
        ((L((i)^*[A])).obj b))))
  -- the unit of `Li^* ⊣ Ri_*` at `i_!K ⊗ᴸ Lg^*L` is an isomorphism
  have hN : IsIso (adj'.unit.app (((-⊗ᴸ-(Z)[A]).obj M).obj ((L((g)^*[A])).obj L))) :=
    adj'.isIso_unit_app_of_iso
      ((((derivedOpenImmersionLowerShriekProjectionIso A i).app K).app
        ((L((g)^*[A])).obj L)).symm ≪≫
        asIso ((derivedOpenImmersionLowerShriekToLowerStar A i).app _))
  exact adj.isIso_rightAdjointProjectionMap_app_app_of_comp _ adj' M L

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

The identity case: the projection formula holds for `f = 𝟙 X`.

The chosen compactification `X ⟶[i] Z ⟶[g] X` of `𝟙 X` need not be trivial, but `i` is then
also a closed immersion, a section of the proper `g`, and the projection map of `Rg_*` at `i_!K`
is an isomorphism by
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_section`. -/
theorem hasProjectionFormula_id (X : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    HasProjectionFormula A (𝟙 X) K L := by
  let c := HasCompactification.compactification (𝟙 X)
  have : IsClosedImmersion c.i := c.isClosedImmersion_openImmersion inferInstance
  exact hasProjectionFormulaOfCompactification_of_isIso A c K L
    (isIso_rightDerivedLowerStarProjectionMap_app_app_of_section A c.i c.g c.comm.symm K L)

end Coherence

section TorsionCoherence

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}}

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

Compatibility of the projection formula with the composition law: if the formula holds for
`f` at `K` and `Lg^* M`, and for `g` at `Rf_! K` and `M`, then it holds for `f ≫ g` at `K`
and `M`. For torsion coefficients the projection formula holds for every morphism admitting a
compactification and all objects (`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`), so
the two hypotheses are not used in the proof; they are kept so that the statement is the
coherence of the blueprint, meaningful for other coefficients. This is the objectwise shadow
of the blueprint's associativity pentagon; the pentagon itself is an identity between canonical
transformations and is not stated, see the module docstring. -/
theorem hasProjectionFormula_comp [Finite Λ] (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hf : HasProjectionFormula (ModuleCat.{u + 1} Λ) f K ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M))
    (_hg : HasProjectionFormula (ModuleCat.{u + 1} Λ) g ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) M) :
    HasProjectionFormula (ModuleCat.{u + 1} Λ) (f ≫ g) K M :=
  hasProjectionFormula_of_finite Λ (f ≫ g) K M

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

Independence of the compactification, for torsion coefficients: the formula computed with an
arbitrary compactification `c` of `f` holds if and only if it holds for the chosen one, i.e. for
`AlgebraicGeometry.Etale.HasProjectionFormula`. For torsion coefficients both sides hold: the
argument for the chosen compactification (`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`)
applies to any compactification. -/
theorem hasProjectionFormulaOfCompactification_iff [Finite Λ] {f : X ⟶ Y}
    [HasCompactification f]
    (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c K L ↔
      HasProjectionFormula (ModuleCat.{u + 1} Λ) f K L := by
  have h (c : Compactification f) :
      HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c K L := by
    have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ c.g
    rw [HasProjectionFormulaOfCompactification, projectionMapOfCompactification_app_app]
    infer_instance
  exact iff_of_true (h c) (h _)

end TorsionCoherence

end Etale

end AlgebraicGeometry
