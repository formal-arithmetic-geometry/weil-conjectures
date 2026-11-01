/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# Composition of the derived lower and upper shrieks on bounded constructible complexes

As in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all
schemes are separated and of finite type over a field `k` of characteristic `p > 0` with
`p ≠ ℓ`, and all morphisms are morphisms of `Over (Spec (.of k))`. For composable morphisms
`f : X ⟶ Y` and `g : Y ⟶ S`, this file gives, for the coefficient rings `E̲` of a finite extension
`E` of `ℚ_ℓ` and `ℚ̲̄_ℓ`, the composition isomorphisms
```
R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!,      R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!
```
on the bounded constructible derived categories.

## The lower shriek

The lower shriek `Rf_!` is defined through the compactification `compactificationOverField f`
chosen for each morphism separately, so the first isomorphism compares three unrelated
compactifications. Write `c = (X ⟶[i] Z ⟶[p] Y)` and `c' = (Y ⟶[j] Z' ⟶[q] S)` for the chosen
compactifications of `f` and `g`, and choose a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')` of
`p ≫ j` whose square
```
Z --i'--> W
|p        |p'
v         v
Y --j---> Z'
```
is cartesian (`Compactification.exists_isPullback_overG_overI`). Then
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S` is a compactification of `f ≫ g` (`Compactification.overComp`), and
```
R(f ≫ g)_! ≅ (i ≫ i')_! ⋙ R(p' ≫ q)_*          (independence of the compactification)
           ≅ i_! ⋙ (i'_! ⋙ Rp'_*) ⋙ Rq_*      (composition of `j_!` and of `Rf_*`)
           ≅ i_! ⋙ (Rp_* ⋙ j_!) ⋙ Rq_*        (the exchange isomorphism)
           = Rf_! ⋙ Rg_!.
```
The *exchange morphism* `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of the cartesian square
(`boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`) is the mate, under the
adjunctions `Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism
`j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!`
(`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`). It is an isomorphism for `p'`
proper.

## The upper shriek

The second isomorphism is the conjugate (`conjugateIsoEquiv`) of the first under the
adjunctions `R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`, the latter being the
composite of `Rf_! ⊣ Rf^!` and `Rg_! ⊣ Rg^!`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`: the
  exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp` and its `_padicAlgCl` version:
  `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.
- `ProEtale.CondensedRing.boundedConstructibleUpperShriekComp` and its `_padicAlgCl` version:
  `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`.

## Main results

- `isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl`: for `ℚ̲̄_ℓ`,
  the exchange morphism is an isomorphism for `p'` proper. It is the exchange
  morphism of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq`).
- `isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`: the same statement for
  `E̲`, by the same argument: the restrictions to `X` and to its closed complement jointly
  reflect isomorphisms; over `X` it follows from the mate calculus and proper base change, and
  over the closed complement both sides vanish.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

section Exchange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The *unit insertion* step of the exchange morphism (`E`-coefficient): the natural transformation
`Rp_* ⋙ j_! ⟶ (Rp_* ⋙ j_!) ⋙ (Lp'^* ⋙ Rp'_*)` obtained by inserting the unit of the adjunction
`Lp'^* ⊣ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep :
    boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.continuousMapRingObj E) ℓ j ⟶
      (boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleOpenImmersionLowerShriek
        (Profinite.continuousMapRingObj E) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ p' ⋙
          boundedConstructibleLowerStar ℓ E p') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction ℓ E p').unit

/-- The *square transport* step of the exchange morphism (`E`-coefficient):
`Functor.squareTransport` applied to the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅
Lp^* ⋙ i'_!` of the cartesian square, under `Rp_*` on the left and `Rp'_*` on the right. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    (sq : IsPullback p i' j p') :
    (boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.continuousMapRingObj E) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ p' ⋙
          boundedConstructibleLowerStar ℓ E p') ≅
      (boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleUpperStar
        (Profinite.continuousMapRingObj E) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ E p') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ E p)
    (boundedConstructibleLowerStar ℓ E p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.continuousMapRingObj E) ℓ
      sq)

/-- The *counit contraction* step of the exchange morphism (`E`-coefficient): the natural
transformation `(Rp_* ⋙ Lp^*) ⋙ (i'_! ⋙ Rp'_*) ⟶ i'_! ⋙ Rp'_*` obtained by contracting the counit of
the adjunction `Lp^* ⊣ Rp_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep :
    (boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj E) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ E p') ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ E p' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E p).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The *exchange morphism* `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` on bounded constructible complexes for
a cartesian square
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` and `i'` open immersions (`E`-coefficient): the mate, under the adjunctions `Lp^* ⊣ Rp_*`
and `Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!`
(`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`), assembled as the composite of the
unit insertion, the square transport, and the counit contraction:
`Rp_* ⋙ j_! ⟶ Rp_* ⋙ j_! ⋙ Lp'^* ⋙ Rp'_* ≅ Rp_* ⋙ Lp^* ⋙ i'_! ⋙ Rp'_* ⟶ i'_! ⋙ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.continuousMapRingObj E) ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ E p' :=
  boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep ℓ E ≫
    (boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep ℓ E sq).hom ≫
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep ℓ E

private lemma exchange_eq_mate (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E sq =
      (mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (TwoSquare.mk _ _ _ _
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
            (Profinite.continuousMapRingObj E) ℓ sq).hom)).natTrans := by
  ext K
  simp [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange,
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep,
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep,
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep,
    mateEquiv, Category.assoc]

-- This is the open–closed argument of the source library’s étale exchange theorem.
private theorem exchangeIsIsoOfComplement
    (sq : IsPullback p i' j p')
    {C P : Over (Spec (.of k))}
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (c : C ⟶ Z) [IsClosedImmersion c.left] (r : P ⟶ Z') (q : P ⟶ C)
    (sqc : IsPullback r q p' c)
    (hc : Set.range c.left.base = (Set.range j.left.base)ᶜ)
    [QuasiCompact j.left]
    [IsIso (boundedConstructibleBaseChange ℓ E sqc.toCommSq)] :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E sq) := by
  have hj := boundedOpenUnitIsIso (Profinite.continuousMapRingObj E) ℓ j
  have hi' := boundedOpenUnitIsIso (Profinite.continuousMapRingObj E) ℓ i'
  have hdisj : Disjoint (Set.range c.left.base) (Set.range j.left.base) := by
    rw [hc]
    exact disjoint_compl_left
  have hdisj' : Disjoint (Set.range r.left.base) (Set.range i'.left.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨u, hu⟩
    refine Set.disjoint_left.1 hdisj ⟨q.left.base a, rfl⟩ ⟨p.left.base u, ?_⟩
    have hw := congrArg Over.Hom.left sq.w
    have hwc := congrArg Over.Hom.left sqc.w
    simp only [Over.comp_left] at hw hwc
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hu,
      ← Scheme.Hom.comp_apply, hwc, Scheme.Hom.comp_apply]
  have point (K : Dᵇc(X'.left)⟦Profinite.continuousMapRingObj E⟧) :
      IsIso ((boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E sq).app K) := by
    let f := (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E sq).app K
    have hopen : IsIso ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        j).map f) := by
      dsimp only [f]
      rw [exchange_eq_mate]
      exact isIso_map_mateEquiv_app_of_isIso
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.continuousMapRingObj E) ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.continuousMapRingObj E) ℓ i')
        (TwoSquare.mk _ _ _ _
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
            (Profinite.continuousMapRingObj E) ℓ sq).hom) K
    suffices hmap : IsIso ((boundedConstructible _).ι.map f) from
      isIso_of_reflects_iso f (boundedConstructible _).ι
    apply (derivedModuleJointIso (Profinite.continuousMapRingObj E) c.left j.left
      (by rw [hc]; simp)).isIso_of_pairFunctor
    · refine isIso_of_source_target_iso_zero _
        (derivedPullbackExtensionZero (Profinite.continuousMapRingObj E) j.left c.left hdisj
          ((boundedConstructibleLowerStar ℓ E p).obj K).obj).isoZero
        (IsZero.isoZero ?_)
      have hN : IsZero ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ r).obj
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
            i').obj K)) :=
        IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _
          (derivedPullbackExtensionZero (Profinite.continuousMapRingObj E) i'.left r.left hdisj'
            K.obj)
      have htarget : IsZero ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          c).obj ((boundedConstructibleLowerStar ℓ E p').obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
              i').obj K))) :=
        ((boundedConstructibleLowerStar ℓ E q).map_isZero hN).of_iso
          (asIso ((boundedConstructibleBaseChange ℓ E sqc.toCommSq).app
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
              i').obj K)))
      exact (boundedConstructible _).ι.map_isZero htarget
    · exact (NatIso.isIso_map_iff
        (boundedConstructibleUpperStarCompatibility (Profinite.continuousMapRingObj E) ℓ j) f).1 (by
          change IsIso ((boundedConstructible _).ι.map
            ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ j).map f))
          infer_instance)
  exact NatIso.isIso_of_isIso_app _

private theorem exchangeIsIsoOfProperBC
    [IsProper p'.left] (sq : IsPullback p i' j p')
    (hBC : ∀ {C P : Over (Spec (.of k))}
      [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
      [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
      (c : C ⟶ Z) (r : P ⟶ Z') (q : P ⟶ C) (sqc : IsPullback r q p' c),
      IsIso (boundedConstructibleBaseChange ℓ E sqc.toCommSq)) :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E sq) := by
  let C : Over (Spec (.of k)) := Over.mk (j.left.closedComplement ≫ Z.hom)
  let c : C ⟶ Z := Over.homMk j.left.closedComplement
  have : IsClosedImmersion c.left := inferInstanceAs (IsClosedImmersion j.left.closedComplement)
  have : LocallyOfFiniteType C.hom := by dsimp [C]; infer_instance
  have : QuasiCompact C.hom := by dsimp [C]; infer_instance
  have : IsSeparated C.hom := by dsimp [C]; infer_instance
  let P : Over (Spec (.of k)) :=
    Over.mk (pullback.snd p'.left c.left ≫ C.hom)
  let r : P ⟶ Z' := Over.homMk (pullback.fst p'.left c.left) (by
    change pullback.fst p'.left c.left ≫ Z'.hom =
      pullback.snd p'.left c.left ≫ C.hom
    rw [← Over.w p', pullback.condition_assoc, Over.w c])
  let q : P ⟶ C := Over.homMk (pullback.snd p'.left c.left)
  have : LocallyOfFiniteType P.hom := by dsimp [P]; infer_instance
  have : QuasiCompact P.hom := by dsimp [P]; infer_instance
  have : IsSeparated P.hom := by dsimp [P]; infer_instance
  have sqc : IsPullback r q p' c :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext pullback.condition)
      (IsPullback.of_hasPullback p'.left c.left)
  have := hBC c r q sqc
  have : QuasiCompact (j.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp j.left Z.hom
  exact exchangeIsIsoOfComplement ℓ E sq c r q sqc j.left.range_closedComplement

end Exchange

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

section Exchange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The *unit insertion* step of the exchange morphism (`𝒪_E`-coefficient): the natural
transformation `Rp_* ⋙ j_! ⟶ (Rp_* ⋙ j_!) ⋙ (Lp'^* ⋙ Rp'_*)` obtained by inserting the unit of the
adjunction `Lp'^* ⊣ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep :
    boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicIntegersRingObj ℓ E) ℓ j ⟶
      (boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicIntegersRingObj ℓ E) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p' ⋙
          boundedConstructibleLowerStar ℓ E p') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction ℓ E p').unit

/-- The *square transport* step of the exchange morphism (`𝒪_E`-coefficient):
`Functor.squareTransport` applied to the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅
Lp^* ⋙ i'_!` of the cartesian square, under `Rp_*` on the left and `Rp'_*` on the right. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    (sq : IsPullback p i' j p') :
    (boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicIntegersRingObj ℓ E) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p' ⋙
          boundedConstructibleLowerStar ℓ E p') ≅
      (boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleUpperStar
        (Profinite.padicIntegersRingObj ℓ E) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ E p') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ E p)
    (boundedConstructibleLowerStar ℓ E p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicIntegersRingObj ℓ E)
      ℓ sq)

/-- The *counit contraction* step of the exchange morphism (`𝒪_E`-coefficient): the natural
transformation `(Rp_* ⋙ Lp^*) ⋙ (i'_! ⋙ Rp'_*) ⟶ i'_! ⋙ Rp'_*` obtained by contracting the counit of
the adjunction `Lp^* ⊣ Rp_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep :
    (boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleUpperStar
      (Profinite.padicIntegersRingObj ℓ E) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ E p') ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ E p' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E p).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The *exchange morphism* `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` on bounded constructible complexes for
a cartesian square
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` and `i'` open immersions (`𝒪_E`-coefficient): the mate, under the adjunctions `Lp^* ⊣ Rp_*`
and `Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!`
(`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`), assembled as the composite of the
unit insertion, the square transport, and the counit contraction:
`Rp_* ⋙ j_! ⟶ Rp_* ⋙ j_! ⋙ Lp'^* ⋙ Rp'_* ≅ Rp_* ⋙ Lp^* ⋙ i'_! ⋙ Rp'_* ⟶ i'_! ⋙ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStar ℓ E p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicIntegersRingObj ℓ E) ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ E p' :=
  boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep ℓ E ≫
    (boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep ℓ E sq).hom ≫
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep ℓ E

end Exchange

end PadicIntegersRingObj

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section ExchangeIsIso

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]

/-- For bounded constructible `E`-sheaves, the exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of
a cartesian square with `p'` proper is an isomorphism: over the open `X ⊆ Z` it is
the identification `Lj^* ⋙ Rp'_* ≅ Rp_* ⋙ Li'^*`, and over the closed complement `Z ∖ X` the stalks
of `Rp'_*(i'_! K)` are, by proper base change, the cohomology of the fibres of `p'` over `Z ∖ X`,
which do not meet `X' ⊆ Z'`, with coefficients in `i'_! K`, hence vanish. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    IsIso (ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      ℓ E sq) := by
  have hex : ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      ℓ E sq = Adjunction.exchangeRight
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
          (Profinite.continuousMapRingObj E) ℓ sq) := by
    unfold ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep
      ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
      ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep
      Adjunction.exchangeRight
    rfl
  have h₁ := isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq.flip
  have h₂ := isIso_boundedConstructibleBaseChange_of_isProper ℓ E
    (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j))
  have : QuasiCompact (j.left ≫ Z.hom) := by
    rw [Over.w j]
    infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp j.left Z.hom
  rw [hex]
  have hK (K : Dᵇc(X'.left)⟦Profinite.continuousMapRingObj E⟧) :
      IsIso ((Adjunction.exchangeRight
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
          (Profinite.continuousMapRingObj E) ℓ sq)).app K) := by
    refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl
      (Profinite.continuousMapRingObj E) ℓ
      (overClosedComplement j) j (isCompl_range_overClosedComplement j) _ ?_ ?_
    · -- Over the open `X`, by the mate calculus and proper base change.
      have : IsIso ((Adjunction.exchangeRight
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
          (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
              sq.toCommSq.flip)).app
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
              i').obj K)) := by
        rw [← ContinuousMapRingObj.boundedConstructibleBaseChange_eq_exchangeRight]
        infer_instance
      exact Adjunction.isIso_map_exchangeRight_app
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.continuousMapRingObj E) ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.continuousMapRingObj E) ℓ i') _ _
        (boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft
          (Profinite.continuousMapRingObj E) ℓ sq.toCommSq) K
    · -- Over the closed complement both sides vanish.
      have hS : Limits.IsZero ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (overClosedComplement j)).obj
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
            j).obj ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p).obj K))) :=
        isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
            (Profinite.continuousMapRingObj E) ℓ j
          (overClosedComplement j) (isCompl_range_overClosedComplement j).disjoint.symm _
      have hT : Limits.IsZero ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (overClosedComplement j)).obj
          ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p').obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
              i').obj K))) :=
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
          (overPullbackSnd p' (overClosedComplement j))).map_isZero
          (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
              (Profinite.continuousMapRingObj E) ℓ i'
            (overPullbackFst p' (overClosedComplement j))
            (disjoint_range_overPullbackFst_overClosedComplement sq.toCommSq) K)).of_iso
          (asIso ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
            (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j)).toCommSq).app
              ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
                  i').obj K)))
      exact ⟨⟨hT.to_ _, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩
  exact NatIso.isIso_of_isIso_app _

end ExchangeIsIso

/-! ### The composition isomorphisms -/

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `E`-sheaves: for the chosen compactifications `c = (X ⟶[i] Z
⟶[p] Y)` of `f` and `c' = (Y ⟶[j] Z' ⟶[q] S)` of `g`, and a compactification `d = (Z ⟶[i'] W ⟶[p']
Z')` of `p ≫ j` with cartesian square (`Compactification.exists_isPullback_overG_overI`), the
composite of the independence of the compactification
(`boundedConstructibleLowerShriekOfCompactificationIso`) for the composite compactification
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S`, of the composition isomorphisms of `j_!` and `Rf_*`, and of the
inverse of the exchange isomorphism `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekComp :
    ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E (f ≫ g) ≅
      ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E g :=
  let c := compactificationOverField f
  let c' := compactificationOverField g
  have hd := Compactification.exists_isPullback_overG_overI c c'
  let d := hd.choose
  let e := Compactification.overCompObjIso c c' d
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper e.hom.left := by
    simp only [e, Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [e]⟩
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E hd.choose_spec
  boundedConstructibleLowerShriekOfCompactificationIso ℓ E _ (c.overComp c' d) ≪≫
    (ContinuousMapRingObj.boundedConstructibleLowerShriekRefinementIso ℓ E sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _
      (ContinuousMapRingObj.boundedConstructibleLowerStarComp ℓ E d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso
        (ContinuousMapRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        ℓ E hd.choose_spec)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for the exceptional inverse image on
bounded constructible `E`-sheaves: the conjugate of
`boundedConstructibleLowerShriekComp` under the adjunctions `R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙
Rg_! ⊣ Rg^! ⋙ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekComp :
    ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E (f ≫ g) ≅
      ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E g ⋙
        ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f :=
  conjugateIsoEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E (f ≫ g))
    ((ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f).comp
      (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g))
    (boundedConstructibleLowerShriekComp ℓ E f g).symm

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for the exceptional inverse image on
bounded constructible `ℚ̄_ℓ`-sheaves: the conjugate of
`boundedConstructibleLowerShriekComp_padicAlgCl` under the adjunctions
`R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekComp_padicAlgCl :
    boundedConstructibleUpperShriek ℓ (f ≫ g) ≅
      boundedConstructibleUpperShriek ℓ g ⋙
        boundedConstructibleUpperShriek ℓ f :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g))
    ((boundedConstructibleUpperShriekAdjunction ℓ f).comp
      (boundedConstructibleUpperShriekAdjunction ℓ g))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).symm

end AlgebraicGeometry.ProEtale.CondensedRing
