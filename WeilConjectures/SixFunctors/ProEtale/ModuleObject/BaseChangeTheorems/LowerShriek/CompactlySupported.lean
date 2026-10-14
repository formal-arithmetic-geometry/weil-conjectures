/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs

/-!

# The compactly supported base change theorem for constructible `E`- and `ℚ̄_ℓ`-sheaves

Let `ℓ` be a prime and `E` a finite extension of `ℚ_ℓ`, with condensed ring `E̲ = C(-, E)`
(`Profinite.continuousMapRingObj E`). Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and compactifications `c : X ⟶[i] Z ⟶[p] Y` of `f` and
`c'` of `f'`. This file deduces from the proper base change theorem
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper`) and base change
for extension by zero
(`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`)
that the compact-support base-change morphism

`Ex_!^{c,c'} : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`

on the bounded constructible derived categories of `E`-sheaves, and of `ℚ̄_ℓ`-sheaves for the
condensed ring `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`, is an isomorphism: first for
`c' = c.baseChange sq`, then for arbitrary `c'` through the identification
`Rf'_!^{c.baseChange sq} ≅ Rf'_!^{c'}`, and in particular for the lower shrieks
`Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` of the chosen compactifications. No properness is imposed
on `f` itself: the properness enters only through the structure morphism `p` of the
compactification.

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes are
separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all
morphisms are morphisms over `Spec k`. The compactification `Z` of `f` and its base change
`Z ×_Y Y'` are then separated and of finite type over `k` as well
(`WeilConjectures.Compactification.Over`).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationBaseChange` and its
  `_padicAlgCl` version: the compact-support base-change morphism `Ex_!^{c,c'}` for arbitrary
  compactifications, the pasting into `c.baseChange sq` followed by the identification
  `Rf'_!^{c.baseChange sq} ≅ Rf'_!^{c'}`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso`, currently
  `sorry`).
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange` and its `_padicAlgCl`
  version: the compact-support base-change morphism `Ex_!` for the chosen compactifications.

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
  and its `_padicAlgCl` version: the case `c' = c.baseChange sq`.
- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekOfCompactificationBaseChange`
  and its `_padicAlgCl` version: the base change theorem for the compactly supported direct
  image of bounded constructible `E`- and `ℚ̄_ℓ`-sheaves, for arbitrary compactifications `c`
  of `f` and `c'` of `f'`.
- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekBaseChange` and its
  `_padicAlgCl` version: the same for the lower shrieks of the chosen compactifications.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [f.IsOver (Spec (.of k))]
  [g.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-! ### Into the base-changed compactification -/

include ℓ k in
/-- The compact-support base-change morphism into the base-changed compactification,
`Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.baseChange sq}`, is an isomorphism of functors
`Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`: in the defining pasting, the direct-image exchange is an isomorphism
by proper base change for the proper structure morphism `p` of `c`, and the extension-by-zero
exchange is an isomorphism by base change for extension by zero. -/
theorem isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f) (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
      (Profinite.continuousMapRingObj E) ℓ k c sq) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper ℓ E k (c.baseChange_isPullback_g sq)
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq]
  infer_instance

/-- The compact-support base-change morphism into the base-changed compactification,
`Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.baseChange sq}`, is an isomorphism of functors
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̲̄_ℓ⟧`. -/
theorem isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_padicAlgCl
    (c : Compactification f) (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
      (Profinite.padicAlgClRingObj ℓ) ℓ k c sq) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ k
    (c.baseChange_isPullback_g sq)
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq]
  infer_instance

/-! ### For arbitrary compactifications -/

/-- The *compact-support base-change morphism* `Ex_!^{c,c'} : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`
on bounded constructible `E`-sheaves, for a cartesian square `sq` and arbitrary compactifications
`c` of `f` and `c'` of `f'`: the pasting
`boundedConstructibleLowerShriekOfCompactificationBaseChangePasting` into the base-changed
compactification `c.baseChange sq`, followed by the identification
`boundedConstructibleLowerShriekOfCompactificationIso` of `Rf'_!^{c.baseChange sq}` with
`Rf'_!^{c'}`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChange
    (c : Compactification f) (c' : Compactification f') (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification (Profinite.continuousMapRingObj E) ℓ k c ⋙
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g' ⋙
        boundedConstructibleLowerShriekOfCompactification
          (Profinite.continuousMapRingObj E) ℓ k c' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChangeOfIso _ ℓ k c c' sq
    (boundedConstructibleLowerShriekOfCompactificationIso ℓ E k (c.baseChange sq) c')

/-- The *compact-support base-change morphism* `Ex_!^{c,c'} : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`
on bounded constructible `ℚ̄_ℓ`-sheaves, for a cartesian square `sq` and arbitrary
compactifications `c` of `f` and `c'` of `f'`: the pasting into the base-changed
compactification followed by the identification
`boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl
    (c : Compactification f) (c' : Compactification f') (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k c ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g' ⋙
        boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k c' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChangeOfIso _ ℓ k c c' sq
    (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ k (c.baseChange sq) c')

include ℓ k in
/-- **The base change theorem for the compactly supported direct image** of bounded
constructible `E`-sheaves, `E` a finite extension of `ℚ_ℓ`, for arbitrary compactifications:
for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and compactifications `c` of `f` and `c'` of `f'`, the compact-support base-change morphism
`Ex_!^{c,c'} : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` is an isomorphism of functors
`Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`. -/
theorem isIso_boundedConstructibleLowerShriekOfCompactificationBaseChange
    (c : Compactification f) (c' : Compactification f') (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ E k c c' sq) := by
  have := isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E k c sq
  dsimp only [boundedConstructibleLowerShriekOfCompactificationBaseChange,
    boundedConstructibleLowerShriekOfCompactificationBaseChangeOfIso]
  infer_instance

/-- **The base change theorem for the compactly supported direct image** of bounded
constructible `ℚ̄_ℓ`-sheaves, for arbitrary compactifications: for a cartesian square of schemes
`sq : IsPullback g' f' f g` and compactifications `c` of `f` and `c'` of `f'`, the
compact-support base-change morphism `Ex_!^{c,c'} : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` is an
isomorphism of functors `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̲̄_ℓ⟧`. -/
theorem isIso_boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl
    (c : Compactification f) (c' : Compactification f') (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl ℓ k c c' sq) := by
  have := isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_padicAlgCl
    ℓ k c sq
  dsimp only [boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl,
    boundedConstructibleLowerShriekOfCompactificationBaseChangeOfIso]
  infer_instance

/-! ### For the chosen compactifications -/

/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `E`-sheaves for a cartesian square `sq`, with the lower shrieks
`boundedConstructibleLowerShriek` for the chosen compactifications
`compactificationOverField k f` of `f` and `compactificationOverField k f'` of `f'`. -/
noncomputable def boundedConstructibleLowerShriekBaseChange (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ k f ⋙
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g' ⋙
        boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ k f' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ E k
    (compactificationOverField k f) (compactificationOverField k f') sq

/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `ℚ̄_ℓ`-sheaves for a cartesian square `sq`, with the lower shrieks
`boundedConstructibleLowerShriek` for the chosen compactifications. -/
noncomputable def boundedConstructibleLowerShriekBaseChange_padicAlgCl
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ k f ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g' ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ k f' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl ℓ k
    (compactificationOverField k f) (compactificationOverField k f') sq

include ℓ k in
/-- **The base change theorem for the compactly supported direct image** of bounded
constructible `E`-sheaves: for a cartesian square of schemes `sq : IsPullback g' f' f g`, the
compact-support base-change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` is an isomorphism of
functors `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`, where `Rf_!` and `Rf'_!` are the lower shrieks for the
chosen compactifications. -/
theorem isIso_boundedConstructibleLowerShriekBaseChange (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekBaseChange ℓ E k sq) :=
  isIso_boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ E k _ _ sq

/-- **The base change theorem for the compactly supported direct image** of bounded
constructible `ℚ̄_ℓ`-sheaves: for a cartesian square of schemes `sq : IsPullback g' f' f g`, the
compact-support base-change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` is an isomorphism of
functors `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̲̄_ℓ⟧`, where `Rf_!` and `Rf'_!` are the lower shrieks for the
chosen compactifications. -/
theorem isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ k sq) :=
  isIso_boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl ℓ k _ _ sq

end AlgebraicGeometry.ProEtale.CondensedRing
