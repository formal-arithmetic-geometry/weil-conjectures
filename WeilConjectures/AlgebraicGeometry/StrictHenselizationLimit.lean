/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal

/-!
# The strict henselization at a non-closed point as a limit of smaller schemes

Let `K` be a field, `X` a scheme of finite type over `K` and `s : Spec Ω ⟶ X` a geometric point
lying over a point `x` with `trdeg_K κ(x) > 0`, equivalently a non-closed point `x`. Let
`X' = Spec 𝒪^{sh}_{X,s}` be the strict localization (`AlgebraicGeometry.Scheme.strictLocalization`;
recall that it is also the limit of the affine pointed étale neighbourhoods of `s`,
`AlgebraicGeometry.Scheme.isLimitStrictLocalizationConeOver`). Then there is a separably closed
field `L` over `K` such that `X'` is an `L`-scheme and a cofiltered limit, with affine transition
maps, of affine schemes `X_i` of finite type over `L` with `dim X_i < dim X`
(blueprint `lem-kun-0f0u`, Stacks 0F0U).

## References

- Stacks Project, Lemma 0F0U, <https://stacks.math.columbia.edu/tag/0F0U>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Blueprint `lem-kun-0f0u`: the strict henselization as a limit.

Let `K` be a field, `aX : X ⟶ Spec K` of finite type and `s : Spec Ω ⟶ X` a geometric point
(`Ω` separably closed) lying over a non-closed point `x` of `X` (for `X` of finite type over `K`
this is equivalent to `trdeg_K κ(x) > 0`). Then there are

* a separably closed field `L` over `K` and a morphism `ℓ : X' ⟶ Spec L` from the strict
  localization `X' = Spec 𝒪^{sh}_{X,s}`, compatible with `X' ⟶ X ⟶ Spec K` and
  `Spec L ⟶ Spec K`;
* a small cofiltered category `I`, a diagram `D : I ⥤ Scheme` and a limit cone `π` from `X'`
  to `D`;
* structure morphisms `q i : D i ⟶ Spec L`, locally of finite type, compatible with the
  transition maps and with `ℓ`,

such that every `D i` is affine, all transition maps are affine, and `dim D i < dim X`. -/
@[stacks 0F0U]
theorem exists_isLimit_strictLocalization_of_not_isClosed {K Ω : Type u} [Field K] [Field Ω]
    [IsSepClosed Ω] {X : Scheme.{u}} (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] (s : Spec (.of Ω) ⟶ X) (hs : ¬ IsClosed {s (IsLocalRing.closedPoint Ω)}) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L) (_ : Algebra K L)
      (ℓ : strictLocalization s ⟶ Spec (.of L))
      (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u}) (π : (Functor.const I).obj (strictLocalization s) ⟶ D)
      (q : ∀ i, D.obj i ⟶ Spec (.of L)),
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = strictLocalizationToBase s ≫ aX ∧
      (∀ i, IsAffine (D.obj i)) ∧ (∀ ⦃i j : I⦄ (f : i ⟶ j), IsAffineHom (D.map f)) ∧
      (∀ i, LocallyOfFiniteType (q i)) ∧ (∀ i, π.app i ≫ q i = ℓ) ∧
      (∀ ⦃i j : I⦄ (f : i ⟶ j), D.map f ≫ q j = q i) ∧
      ∀ i, topologicalKrullDim (D.obj i) < topologicalKrullDim X :=
  sorry

end AlgebraicGeometry.Scheme
