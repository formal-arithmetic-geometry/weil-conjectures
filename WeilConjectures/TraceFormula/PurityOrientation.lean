/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothRelativeDimensionCover
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomUnitTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCoverIsIso
public import WeilConjectures.TraceFormula.PurityBaseChangeRestriction
public import WeilConjectures.TraceFormula.PurityOrientationPure

/-!

# The relative dualizing complex of a smooth morphism

For a smooth morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, the *relative
dualizing complex* `ω_f = Rf^! ℚ̄_ℓ` on `X` is the object through which smooth purity is
expressed: `Rf^! K ≅ Lf^* K ⊗ ω_f` (`ProEtale.CondensedRing.upperShriekUnitTensorMap`). This file
records the two properties of `ω_f` (its *orientation*, blueprint `sk-prop-sp-orientation`,
`sk-prop-cohsm`) which the proof of smooth purity for `ℚ̄_ℓ`-coefficients takes as input:

- `ProEtale.CondensedRing.isDualizable_upperShriek_unit_of_smooth`: `ω_f` is dualizable;
- `ProEtale.CondensedRing.isIso_upperShriekBaseChange_unit_of_smooth`: the formation of `ω_f`
  commutes with base change.

Both are consequences of the trace isomorphism `ω_f ≅ ℚ̄_ℓ(d)[2d]` of a morphism smooth of pure
relative dimension `d` (`ProEtale.CondensedRing.isIso_smoothPurityMap`, built from the smooth trace
`ProEtale.CondensedRing.smoothTrace` of `WeilConjectures.SmoothPurity.Defs`), of the invertibility
of the Tate twists `ℚ̄_ℓ(d)` (blueprint `sk-def-sp-tate-twist`: "each `Λ_X(1)` is locally free of
rank one") and of the compatibility of the smooth trace with base change (SGA 4, Exposé XVIII,
Théorème 2.9 (Var 4)). Neither the smooth trace nor the comparison isomorphisms of Tate twists
along pullbacks are available (see the module docstring of `WeilConjectures.SmoothPurity.Defs`
and of `WeilConjectures.TateTwist.ProEtale`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- **The relative dualizing complex of a smooth morphism is dualizable** (blueprint
`sk-prop-sp-orientation`, `sk-prop-cohsm`: "`ω_f` is pro-étale locally isomorphic to
`Λ_X(d)[2d]`"): for `f` smooth, `Rf^! ℚ̄_ℓ` is a dualizable object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. On the open
and closed subscheme where `f` has relative dimension `d` it is `ℚ̄_ℓ(d)[2d]` by the trace
(`isIso_smoothPurityMap`), and the Tate twist `ℚ̄_ℓ(d)` is invertible. -/
theorem isDualizable_upperShriek_unit_of_smooth (f : X ⟶ Y) [Smooth f.left] :
    IsDualizable ((boundedConstructibleUpperShriek ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  obtain ⟨ι, _, U, hU, hd⟩ := exists_finite_openCover_smoothOfRelativeDimension f
  refine isDualizable_of_isIso_ihomUnitTensorToIhom ℓ _
    (isIso_of_isIso_upperStar_overRestrictι ℓ U hU _ fun i ↦ ?_)
  obtain ⟨d, hd⟩ := hd i
  refine isIso_map_ihomUnitTensorToIhom_of_isDualizable ℓ (overRestrictι X (U i)) _ ?_
  exact (isDualizable_upperShriek_unit_of_smoothOfRelativeDimension ℓ
    (overRestrictι X (U i) ≫ f) d).of_iso
      ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ (overRestrictι X (U i)) f).app _ ≪≫
        (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ (overRestrictι X (U i))).app _)

/-- **The formation of the relative dualizing complex of a smooth morphism commutes with base
change** (blueprint `sk-prop-cohsm`, (G12) at the unit: "it identifies `g'^* ω_f` with `ω_{f'}`";
`det-sp-purity-bc-factors` (1); SGA 4, Exposé XVIII, Théorème 2.9 (Var 4), the compatibility of
the smooth trace with base change): for a cartesian square with `f` smooth, the exceptional base
change map at the unit `Lg'^* Rf^! ℚ̄_ℓ ⟶ Rf'^! Lg^* ℚ̄_ℓ` is an isomorphism. -/
theorem isIso_upperShriekBaseChange_unit_of_smooth {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [Smooth f.left] :
    IsIso (upperShriekBaseChange ℓ sq (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  obtain ⟨ι, _, U, hU, hd⟩ := exists_finite_openCover_smoothOfRelativeDimension f
  -- the restriction `o' i : (U i) ×_Y Y' ⟶ X'` of the square to the open `U i`
  let o' (i : ι) : pullback (overRestrictι X (U i) ≫ f) g ⟶ X' :=
    sq.lift (pullback.fst (overRestrictι X (U i) ≫ f) g ≫ overRestrictι X (U i))
      (pullback.snd (overRestrictι X (U i) ≫ f) g) (by rw [Category.assoc, pullback.condition])
  have sqo (i : ι) : IsPullback (pullback.fst (overRestrictι X (U i) ≫ f) g).left (o' i).left
      (overRestrictι X (U i)).left g'.left := by
    have t := IsPullback.of_hasPullback (overRestrictι X (U i) ≫ f) g
    rw [← sq.lift_snd (pullback.fst (overRestrictι X (U i) ≫ f) g ≫ overRestrictι X (U i))
      (pullback.snd (overRestrictι X (U i) ≫ f) g)
      (by rw [Category.assoc, pullback.condition])] at t
    have h := IsPullback.of_bot t (sq.lift_fst _ _ _).symm sq
    simpa only [Over.forget_map] using h.map (Over.forget _)
  have : ∀ i, IsOpenImmersion (o' i).left := fun i ↦
    MorphismProperty.of_isPullback (sqo i) inferInstance
  refine isIso_of_isIso_upperStar_of_isOpenImmersion ℓ o' ?_ _ fun i ↦ ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, hi⟩ : ∃ i, g'.left.base x ∈ U i := by
      have : g'.left.base x ∈ (⨆ i, U i : X.left.Opens) := by rw [hU]; trivial
      simpa using this
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    have hr : Set.range (o' i).left.base =
        g'.left.base ⁻¹' Set.range (overRestrictι X (U i)).left.base := by
      rw [← (sqo i).isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp,
        Function.Surjective.range_comp (f := ⇑(sqo i).isoPullback.hom.base)
          (sqo i).isoPullback.hom.homeomorph.surjective, Scheme.Pullback.range_snd]
    rw [hr, range_overRestrictι]
    exact hi
  · obtain ⟨d, hd⟩ := hd i
    have : SmoothOfRelativeDimension d (pullback.snd (overRestrictι X (U i) ≫ f) g).left :=
      have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
      MorphismProperty.of_isPullback (isPullback_pullback_left _ g) hd
    have := isIso_upperShriekBaseChange_unit_of_smoothOfRelativeDimension ℓ
      (IsPullback.of_hasPullback (overRestrictι X (U i) ≫ f) g) d
    exact (isIso_upperStar_map_upperShriekBaseChange_unit_iff ℓ sq (overRestrictι X (U i))).2 this

end AlgebraicGeometry.ProEtale.CondensedRing
