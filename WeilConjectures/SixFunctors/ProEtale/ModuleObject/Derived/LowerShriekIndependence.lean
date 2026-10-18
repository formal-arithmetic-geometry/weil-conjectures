/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Compactification.OverRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange

/-!

# Independence of the lower shriek of `E`- and `ℚ̄_ℓ`-sheaves from the compactification

Let `ℓ` be a prime and `E` a finite extension of `ℚ_ℓ`, with condensed ring `E̲ = C(-, E)`
(`Profinite.continuousMapRingObj E`), and let `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`. For a
compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`, the lower shriek on bounded constructible
complexes is `Rf_!^c := i_! ⋙ Rp_*`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification`). This file shows
that, for the coefficient rings `E̲` and `ℚ̲̄_ℓ`, it does not depend on the compactification: for
two compactifications `c₁` and `c₂` of `f`, `Rf_!^{c₁} ≅ Rf_!^{c₂}`.

These isomorphisms identify the lower shriek attached to an arbitrary compactification with the
lower shriek `Rf_!` for the chosen compactification
(`ProEtale.CondensedRing.boundedConstructibleLowerShriek`), as used in the compact-support
base-change morphism `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange`.

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes
are separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all
morphisms are morphisms of `Over (Spec (.of k))`.

## The construction

Let `c = (X ⟶[i] Z ⟶[p] Y)` and `c₁ = (X ⟶[i₁] Z₁ ⟶[p₁] Y)` be compactifications of `f` and
`h : Z ⟶ Z₁` a refinement: a morphism with `h ≫ p₁ = p` whose square
```
X --i--> Z
|𝟙       |h
v        v
X --i₁-> Z₁
```
is cartesian, that is `h⁻¹(X) = X` (`Compactification.OverRefinement`).

1. The exchange morphism `R(𝟙 X)_* ⋙ i₁_! ⟶ i_! ⋙ Rh_*` of this square
   (`boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'`) is an isomorphism for `h`
   proper, by interchanging proper direct image and extension by zero
   (`isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'`).
2. Then `Rf_!^{c₁} = i₁_! ⋙ Rp₁_* ≅ R(𝟙 X)_* ⋙ i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rh_* ⋙ Rp₁_* ≅ i_! ⋙ Rp_*`,
   through `R(𝟙 X)_* ≅ 𝟭` and the composition isomorphism `Rh_* ⋙ Rp₁_* ≅ R(h ≫ p₁)_*`
   (`boundedConstructibleLowerShriekRefinementIso'`).

Any two compactifications `c₁` and `c₂` of `f` have a common refinement `c`
(`Compactification.exists_overRefinement`), and `Rf_!^{c₁} ≅ Rf_!^c ≅ Rf_!^{c₂}`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekRefinementIso'`: `Rf_!^{c₁} ≅ Rf_!^c`
  along a refinement, for any `Λ` for which the exchange morphism is an isomorphism.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl`: the
  isomorphism `Rf_!^{c₁} ≅ Rf_!^{c₂}` for `E`- and `ℚ̄_ℓ`-sheaves.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The comparison along a refinement -/

section Refinement

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z Z₁ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- The isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement `h : Z ⟶ Z₁` with
`h ≫ p₁ = p` and cartesian square `sq`, when the exchange morphism
`R(𝟙 X)_* ⋙ i₁_! ⟶ i_! ⋙ Rh_*` of `sq` is an isomorphism: the composite
```
i₁_! ⋙ Rp₁_* ≅ (R(𝟙 X)_* ⋙ i₁_!) ⋙ Rp₁_* ≅ (i_! ⋙ Rh_*) ⋙ Rp₁_* ≅ i_! ⋙ R(h ≫ p₁)_* = i_! ⋙ Rp_*
```
of `R(𝟙 X)_* ≅ 𝟭` (`boundedConstructibleLowerStarId`), the exchange isomorphism and the
composition isomorphism `boundedConstructibleLowerStarComp`. For compactifications `c` and `c₁`
of `f` with `i = c.overI`, `p = c.overG`, `i₁ = c₁.overI` and `p₁ = c₁.overG`, it is an
isomorphism `Rf_!^{c₁} ≅ Rf_!^c`. -/
noncomputable def boundedConstructibleLowerShriekRefinementIso'
    [IsFinitenessCoefficient ℓ Λ] (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' Λ ℓ sq)] :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙ boundedConstructibleLowerStar Λ ℓ p₁ ≅
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i ⋙ boundedConstructibleLowerStar Λ ℓ p :=
  Functor.isoWhiskerRight ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleLowerStarId Λ ℓ X).symm _ ≪≫
      asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' Λ ℓ sq)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp Λ ℓ h p₁ ≪≫ eqToIso (by rw [wp]))

end Refinement

/-! ### Independence of the compactification -/

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y}

/-- The *independence of the lower shriek from the compactification* for bounded constructible
`E`-sheaves: for two compactifications `c₁` and `c₂` of `f`, the isomorphism
`Rf_!^{c₁} ≅ Rf_!^{c₂}` between `i₁_! ⋙ Rp₁_*` and `i₂_! ⋙ Rp₂_*` on `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧`:
for a common refinement `c` of `c₁` and `c₂` (`Compactification.exists_overRefinement`), the
composite `Rf_!^{c₁} ≅ Rf_!^c ≅ Rf_!^{c₂}` of the isomorphisms
`boundedConstructibleLowerShriekRefinementIso'` along the refinements. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationIso'
    (c₁ c₂ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactification (Profinite.continuousMapRingObj E) ℓ c₁ ≅
      boundedConstructibleLowerShriekOfCompactification (Profinite.continuousMapRingObj E) ℓ c₂ :=
  have hc := Compactification.exists_overRefinement c₁ c₂
  let r₁ := hc.choose_spec.1.some
  let r₂ := hc.choose_spec.2.some
  have := r₁.isProper
  have := r₂.isProper
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ E r₁.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ E r₂.isPullback
  boundedConstructibleLowerShriekRefinementIso' _ ℓ r₁.isPullback r₁.hom_overG ≪≫
    (boundedConstructibleLowerShriekRefinementIso' _ ℓ r₂.isPullback r₂.hom_overG).symm

/-- The *independence of the lower shriek from the compactification* for bounded constructible
`ℚ̄_ℓ`-sheaves: for two compactifications `c₁` and `c₂` of `f`, the isomorphism
`Rf_!^{c₁} ≅ Rf_!^{c₂}` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`, through a common refinement as in
`boundedConstructibleLowerShriekOfCompactificationIso'`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl
    (c₁ c₂ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ c₁ ≅
      boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ c₂ :=
  have hc := Compactification.exists_overRefinement c₁ c₂
  let r₁ := hc.choose_spec.1.some
  let r₂ := hc.choose_spec.2.some
  have := r₁.isProper
  have := r₂.isProper
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    r₁.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    r₂.isPullback
  boundedConstructibleLowerShriekRefinementIso' _ ℓ r₁.isPullback r₁.hom_overG ≪≫
    (boundedConstructibleLowerShriekRefinementIso' _ ℓ r₂.isPullback r₂.hom_overG).symm

end AlgebraicGeometry.ProEtale.CondensedRing
