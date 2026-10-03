/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Stability properties of the base change property

This file proves the formal stability properties of the base change property
`AlgebraicGeometry.Etale.HasTorsionBaseChange` (`PBC`) which the reduction of the proper base
change theorem to the projective line uses:

- finite morphisms satisfy `PBC` (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isFinite`);
- `PBC` is stable under composition (`AlgebraicGeometry.Etale.HasTorsionBaseChange.comp`);
- `PBC` cancels along a proper surjection
  (`AlgebraicGeometry.Etale.HasTorsionBaseChange.of_comp_of_surjective`);
- `PBC` is local on the target for the étale topology
  (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_jointlySurjective`).

## Main statements

- `AlgebraicGeometry.Etale.HasTorsionBaseChange.comp`: if `f` and `h` satisfy `PBC`, so does
  `f ≫ h`.
- `AlgebraicGeometry.Etale.HasTorsionBaseChange.of_comp_of_surjective`: if `f` is proper and
  surjective and `f`, `f ≫ h` satisfy `PBC`, so does `h`.

## References

- Stacks Project, Lemma 59.91.7, composition, <https://stacks.math.columbia.edu/tag/0A4D>
- Stacks Project, Lemma 59.91.8, cancellation, <https://stacks.math.columbia.edu/tag/0A4C>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y Z : Scheme.{u}}

/-- **Higher direct images of torsion objects are torsion**: for a quasi-compact and
quasi-separated morphism `f : X ⟶ Y`, the derived pushforward `Rf_*` sends objects of
`D⁺(X_ét, Λ)` with torsion cohomology to objects with torsion cohomology. -/
theorem Etale.DerivedCategory.Plus.torsionHomology_rightDerivedFunctorPlus_lowerStar
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ X K) :
    Etale.DerivedCategory.Plus.torsionHomology Λ Y
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K) :=
  sorry

/-- **Finite morphisms satisfy the base change property.**
(blueprint: `prop-weil-pbc-finite-morphism`) -/
theorem Etale.hasTorsionBaseChange_of_isFinite (f : X ⟶ Y) [IsFinite f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_isBaseChangeIso Λ f

/-- **Composition stability**: if `f : X ⟶ Y` and `h : Y ⟶ Z` satisfy the base change property
and `f` is quasi-compact and quasi-separated, then `f ≫ h` satisfies the base change property.
(blueprint: `prop-weil-pbc-composition-stability`) -/
@[stacks 0A4D]
theorem Etale.HasTorsionBaseChange.comp {f : X ⟶ Y} {h : Y ⟶ Z} [QuasiCompact f]
    [QuasiSeparated f] (hf : Etale.HasTorsionBaseChange Λ f)
    (hh : Etale.HasTorsionBaseChange Λ h) :
    Etale.HasTorsionBaseChange Λ (f ≫ h) :=
  sorry

/-- **The base change property implies injective acyclicity.** -/
theorem Etale.hasInjectiveAcyclicity_of_hasTorsionBaseChange {f : X ⟶ Y}
    (hf : Etale.HasTorsionBaseChange Λ f) : Etale.HasInjectiveAcyclicity Λ f :=
  sorry

/-- **Composition of proper maps**: injective acyclicity is stable under composition of
proper morphisms. (blueprint: `lemma-weil-pbc-composition`) -/
@[stacks 0A4D]
theorem Etale.HasInjectiveAcyclicity.comp {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f] [IsProper h]
    (hf : Etale.HasInjectiveAcyclicity Λ f) (hh : Etale.HasInjectiveAcyclicity Λ h) :
    Etale.HasInjectiveAcyclicity Λ (f ≫ h) :=
  Etale.hasInjectiveAcyclicity_of_hasTorsionBaseChange Λ
    ((Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity Λ f hf).comp Λ
      (Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity Λ h hh))

/-- **Vanishing descends to a retract**: if `K` is a retract of `M`, and the derived base
change map is an isomorphism at `M`, then it is an isomorphism at `K`.
(blueprint: `lem-weil-pbc-vanishing-descends-retract`) -/
theorem Etale.isIso_derivedBaseChangeMapPlus_app_of_retract {X' Y' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    {K M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (r : Retract K M)
    (hM : IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app M)) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K) :=
  (MorphismProperty.isomorphisms _).of_retract (NatTrans.retractArrowApp _ r) hM

/-- **Retract supplied by a surjection**: for a surjective morphism `f : X ⟶ Y` and an
injective sheaf `I` on `Y_ét`, the complex `I[0]` is a retract of `Rf_*(f^* I[0])`.
(blueprint: `lem-weil-pbc-retract-supplied`) -/
theorem Etale.nonempty_retract_singleFunctor_rightDerivedFunctorPlus (f : X ⟶ Y)
    [Surjective f] (I : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
    Nonempty (Retract
      ((DerivedCategory.Plus.singleFunctor _ 0).obj I)
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((f)^*[ModuleCat.{u + 1} Λ].obj I)))) :=
  sorry

/-- **Cancellation along a proper surjection**: let `f : X ⟶ Y` be proper and surjective and
`h : Y ⟶ Z` proper. If `f` and `f ≫ h` satisfy the base change property, so does `h`.
(blueprint: `lemma-weil-pbc-cancellation`) -/
@[stacks 0A4C]
theorem Etale.HasTorsionBaseChange.of_comp_of_surjective {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f]
    [Surjective f] [IsProper h] (hf : Etale.HasTorsionBaseChange Λ f)
    (hfh : Etale.HasTorsionBaseChange Λ (f ≫ h)) :
    Etale.HasTorsionBaseChange Λ h :=
  sorry

/-- **Target locality**: for a proper morphism `f : X ⟶ Y`, the base change property is local
on `Y` for the étale topology: if `v i : V i ⟶ Y` is a jointly surjective family of étale
morphisms and every base change `X ×_Y V i ⟶ V i` satisfies the base change property, so
does `f`. (blueprint: `lemma-weil-pbc-target-locality`) -/
theorem Etale.hasTorsionBaseChange_of_jointlySurjective (f : X ⟶ Y) [IsProper f]
    {ι : Type u} {V : ι → Scheme.{u}} (v : ∀ i, V i ⟶ Y) [∀ i, Etale (v i)]
    (hv : ∀ y : Y, ∃ i, y ∈ Set.range (v i))
    (h : ∀ i, Etale.HasTorsionBaseChange Λ (pullback.snd f (v i))) :
    Etale.HasTorsionBaseChange Λ f :=
  sorry

end AlgebraicGeometry
