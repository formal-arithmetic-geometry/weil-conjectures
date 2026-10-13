/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Deligne's generic constructibility for an open immersion

Let `S` be an integral scheme of finite type over a field `k`, let `Λ` be a finite ring whose
exponent is invertible on `S`, let `j : X ⟶ Y` be an open immersion of finite-type `S`-schemes and
let `F` be a constructible sheaf of `Λ`-modules on `X_ét`. Deligne's generic constructibility
theorem (SGA 4½, [Th. finitude], Thm. 1.9) says that over a nonempty open `U ⊆ S` the direct
image `Rj_* F` is bounded constructible and its formation commutes with every base change
`T ⟶ U` from a noetherian scheme.

The property "over `U`, the direct image is bounded constructible and commutes with base
change" is `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn`. It is phrased
through all cartesian squares over noetherian `T ⟶ S` with image in `U`: taking for `T` the open
subscheme `U` itself gives the bounded constructibility of `Rj_{U,*}(F|_{X_U})`, and the base
change map along `Y_T ⟶ Y` is the composite of the one along `Y_T ⟶ Y_U` with the base change
map along the open immersion `Y_U ⟶ Y`, which is an isomorphism.

## Main statements

- `AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn`: Deligne's generic
  constructibility (`thm-fin-deligne-generic-open`).
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field`
  :
  over a field, `Rj_* F` is bounded constructible (`cor-fin-deligne-open-over-field`).
- `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective`:
  descent of the property along a finite, surjective, radicial base change
  (`lem-fin-radicial-exchange-descent`).

## Implementation notes

The blueprint states the theorem and its corollary over a field for `𝔽_ℓ`-coefficients, and
obtains arbitrary finite coefficients `Λ` by a dévissage
(`cor-fin-deligne-open-finite-coefficients`, `lem-fin-coefficients-forgetful-direct-image`). Its
proof applies verbatim to any finite `Λ` whose exponent is invertible on `S`, and we state it in
that generality.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Over a subset `U` of `S`, the derived direct image of the sheaf `F` along `j : X ⟶ Y`, for
`Y` over `S` via `fY`, is bounded constructible and its formation commutes with every base
change from a noetherian scheme: for every noetherian `T`, every `t : T ⟶ S` with image in `U`
and all cartesian squares

```
  X_T --g'--> X
   |          |
  j_T         j
   ↓          ↓
  Y_T --g---> Y
   |          |
  f_T         fY
   ↓          ↓
   T ---t---> S
```

the direct image `Rj_{T,*}(g'^* F)` is bounded constructible and the derived base change map
`g^* Rj_* F ⟶ Rj_{T,*} g'^* F` is an isomorphism. -/
def HasConstructibleDirectImageBaseChangeOn {S X Y : Scheme.{u}} (fY : Y ⟶ S) (j : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Set S) : Prop :=
  ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S), Set.range t ⊆ U →
    ∀ (YT XT : Scheme.{u}) (g : YT ⟶ Y) (fT : YT ⟶ T) (g' : XT ⟶ X) (jT : XT ⟶ YT),
      IsPullback g fT fY t → ∀ sq : IsPullback g' jT j g,
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YT
          ((R((jT)_*[ModuleCat.{u + 1} Λ])).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
        IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))

variable {Λ}

lemma HasConstructibleDirectImageBaseChangeOn.mono {S X Y : Scheme.{u}} {fY : Y ⟶ S}
    {j : X ⟶ Y} {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {U V : Set S}
    (h : HasConstructibleDirectImageBaseChangeOn Λ fY j F U) (hVU : V ⊆ U) :
    HasConstructibleDirectImageBaseChangeOn Λ fY j F V :=
  fun T _ t ht ↦ h T t (ht.trans hVU)

variable (Λ) [Finite Λ]

/-- Blueprint `thm-fin-deligne-generic-open`: Generic bounded constructibility for an open
immersion.

Let `S` be integral and of finite type over a field `k`, let `Λ` be a finite ring whose exponent
is invertible on `S` (the blueprint takes `Λ = 𝔽_ℓ` with `ℓ ≠ char k`), and let `j : X ⟶ Y` be
an open immersion of finite-type `S`-schemes. For a constructible sheaf `F` of `Λ`-modules on
`X`, there is a nonempty open `U ⊆ S` such that `Rj_{U,*}(F|_{X_U})` is bounded constructible
and, for every morphism `T ⟶ U` with noetherian `T`, its base change morphism
`(Rj_{U,*} F|_{X_U})|_{Y_T} ⟶ Rj_{T,*}(F|_{X_T})` is an isomorphism; see
`AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn` for the formulation. -/
theorem exists_hasConstructibleDirectImageBaseChangeOn {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (fY : Y ⟶ S) [LocallyOfFiniteType fY]
    [QuasiCompact fY] (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      HasConstructibleDirectImageBaseChangeOn Λ fY j F U :=
  sorry

/-- Blueprint `lem-fin-radicial-exchange-descent`: Descending the exchange property through a
universal homeomorphism.

Let `π : S' ⟶ S` be finite, surjective and radicial (universally injective), let `j : X ⟶ Y`
be an open immersion of `S`-schemes and `F` a sheaf of `Λ`-modules on `X`. Form the base changes
`Y' = Y ×_S S'` and `X' = X ×_Y Y'`, with the open immersion `j' : X' ⟶ Y'`. If over `S'` the
direct image `Rj'_*(F|_{X'})` is bounded constructible and its formation commutes with every base
change from a noetherian scheme, then the same holds over `S`. -/
theorem HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective
    {S S' X Y X' Y' : Scheme.{u}} (π : S' ⟶ S) [IsFinite π] [Surjective π]
    [UniversallyInjective π] (fY : Y ⟶ S) (j : X ⟶ Y) [IsOpenImmersion j] (g : Y' ⟶ Y)
    (fY' : Y' ⟶ S') (hY : IsPullback g fY' fY π) (g' : X' ⟶ X) (j' : X' ⟶ Y')
    (hX : IsPullback g' j' j g) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : HasConstructibleDirectImageBaseChangeOn Λ fY' j'
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj F) Set.univ) :
    HasConstructibleDirectImageBaseChangeOn Λ fY j F Set.univ :=
  sorry

/-- Blueprint `cor-fin-deligne-open-over-field`: Higher open direct images over a field.

Let `k` be a field, let `Λ` be a finite ring whose exponent is invertible in `k` (the blueprint
takes `Λ = 𝔽_ℓ` with `ℓ ≠ char k`), let `j : X ⟶ Y` be an open immersion of finite-type
`k`-schemes and let `F` be a constructible sheaf of `Λ`-modules on `X`. Then `Rj_* F` is
bounded constructible. This is `thm-fin-deligne-generic-open` over `S = Spec k`, whose only
nonempty open is `S` itself. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field {k : Type u}
    [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] (j : X ⟶ Y)
    [IsOpenImmersion j] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  obtain ⟨U, ⟨s, hs⟩, h⟩ := exists_hasConstructibleDirectImageBaseChangeOn Λ
    (𝟙 (Spec (.of k))) aY j F
  have hU : Set.range (𝟙 (Spec (.of k))) ⊆ (U : Set (Spec (.of k))) := by
    rintro x -
    rwa [Subsingleton.elim x s]
  have := (h (Spec (.of k)) (𝟙 _) hU Y X (𝟙 Y) aY (𝟙 X) j (IsPullback.id_horiz aY)
    (IsPullback.id_horiz j)).1
  exact ObjectProperty.prop_of_iso _ ((R((j)_*[ModuleCat.{u + 1} Λ])).mapIso
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).app _)) this

end Etale

end AlgebraicGeometry
