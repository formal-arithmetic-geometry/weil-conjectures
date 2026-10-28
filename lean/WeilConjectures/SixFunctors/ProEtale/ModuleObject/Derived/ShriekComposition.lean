/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper

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
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_continuousMap` and its
  `_padicAlgCl` version: `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.
- `ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_continuousMap` and its
  `_padicAlgCl` version: `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`.

## Inputs

The exchange is proved by open–closed conservativity. On the open, the generic mate lemma
and full faithfulness of extension by zero apply. On the closed complement, proper base
change identifies the target with a pushforward of a zero restriction. The extension-by-zero
base-change isomorphism remains an input from `LowerShriek.MorphismDefs`. The coefficient-specific
input is the existing proper base change theorem, for `E` and for `ℚ̄_ℓ` respectively.
The composition construction also uses `Compactification.exists_isPullback_overG_overI`
for the existence of the compactification `d`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- Exact derivation and restriction to a full subcategory preserve full faithfulness.
private theorem boundedOpenUnitIsIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    IsIso (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit := by
  have := openUnitIsIso Λ j.left
  have hd : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have ff := Adjunction.fullyFaithfulLOfIsIsoUnit
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left)
  have := ff.full
  have := ff.faithful
  have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).Full := by
    unfold boundedConstructibleOpenImmersionLowerShriek
    infer_instance
  have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).Faithful := by
    unfold boundedConstructibleOpenImmersionLowerShriek
    infer_instance
  exact Adjunction.unit_isIso_of_L_fully_faithful _

set_option backward.isDefEq.respectTransparency false in
private theorem openRestrictionPushforwardZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsZero ((upperStar Λ j).obj ((lowerStar Λ i).obj M)) := by
  have hdisjoint : Set.range i.base ∩ Set.range j.base = ∅ := by
    exact Set.disjoint_iff_inter_eq_empty.mp hij
  have hz : IsZero ((ProEtale.openImmersionRestriction Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) := by
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨T⟩
    let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j)).obj T)
    have hempty : IsEmpty V.left := by
      refine ⟨fun z ↦ ?_⟩
      have hz : (pullback.fst (T.hom ≫ j) i ≫ T.hom ≫ j).base z ∈
          Set.range i.base ∩ Set.range j.base := by
        refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) i z), ?_⟩⟩
        · rw [pullback.condition]
          exact ⟨_, rfl⟩
        · rfl
      rw [hdisjoint] at hz
      exact hz
    exact (isZero_zero Ab.{u + 1}).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X V).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  have hz' : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) :=
    hz.of_iso ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  have hz'' := hz'.of_iso ((profinitePointModuleForgetPullbackIso Λ j).app
    ((lowerStar Λ i).obj M))
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget (condensedRingObj Λ U)).map_injective
  exact hz''.eq_of_src _ _


private theorem pullbackExtensionZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U W : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)
    (hgj : Disjoint (Set.range g.base) (Set.range j.base))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsZero ((upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply ((upperStarLowerStarAdjunction Λ g).homEquiv _ _).injective
  apply ((openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _).injective
  exact (openRestrictionPushforwardZero Λ g j hgj _).eq_of_tgt _ _

private theorem derivedPullbackExtensionZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U W : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)
    (hgj : Disjoint (Set.range g.base) (Set.range j.base))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    IsZero (L((g)^*⟦Λ⟧).obj (D((j)_!open⟦Λ⟧).obj K)) := by
  have hz : IsZero (D((g)^*⟦Λ⟧).obj (D((j)_!open⟦Λ⟧).obj K)) :=
    Functor.isZero_mapDerivedCategory_obj _ _ fun n ↦
      (pullbackExtensionZero Λ j g hgj
        ((DerivedCategory.homologyFunctor _ n).obj K)).of_iso
        ((g)^*⟦Λ⟧.mapIso
          (((j)_!open⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).symm.app K))
  exact hz.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).app _)

private theorem moduleJointZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hi : IsZero ((upperStar Λ i).obj M))
    (hj : IsZero ((upperStar Λ j).obj M)) : IsZero M := by
  have hzj : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj M.X) :=
    ((Mod.forget _).map_isZero hj).of_iso
      ((profinitePointModuleForgetPullbackIso Λ j).app M).symm
  have hzi : IsZero ((ProEtale.upperStar Ab.{u + 1} i).obj M.X) :=
    ((Mod.forget _).map_isZero hi).of_iso
      ((profinitePointModuleForgetPullbackIso Λ i).app M).symm
  have := (ProEtale.abelian_closed_support i j hij).2 M.X hzj
  have hzM : IsZero M.X :=
    ((ProEtale.lowerStar Ab.{u + 1} i).map_isZero hzi).of_iso
      (asIso ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app M.X))
  apply (IsZero.iff_id_eq_zero _).2
  exact Mod.hom_ext _ _ (hzM.eq_of_src _ _)

private theorem moduleJointIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    JointlyReflectIsomorphisms (pairFunctor (upperStar Λ i) (upperStar Λ j)) := by
  refine jointlyReflectIsomorphisms_pairFunctor _ _ fun M N φ hi hj ↦ ?_
  have := hi
  have := hj
  have hker {W : Scheme.{u}} (g : W ⟶ X) [IsIso ((upperStar Λ g).map φ)] :
      IsZero ((upperStar Λ g).obj (kernel φ)) :=
    (isZero_kernel_of_mono ((upperStar Λ g).map φ)).of_iso (PreservesKernel.iso _ φ)
  have hcoker {W : Scheme.{u}} (g : W ⟶ X) [IsIso ((upperStar Λ g).map φ)] :
      IsZero ((upperStar Λ g).obj (cokernel φ)) :=
    (isZero_cokernel_of_epi ((upperStar Λ g).map φ)).of_iso (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (moduleJointZero Λ i j hij _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (moduleJointZero Λ i j hij _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ

private theorem derivedModuleJointIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    JointlyReflectIsomorphisms (pairFunctor L((i)^*⟦Λ⟧) L((j)^*⟦Λ⟧)) :=
  (Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory _ _
    (moduleJointIso Λ i j hij)).pairFunctor_of_iso
    (leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm


/-! ### The exchange morphism -/

section Exchange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsFinitenessCoefficient ℓ Λ]

include ℓ k

/-- The *unit insertion* step of the exchange morphism: the natural transformation
`Rp_* ⋙ j_! ⟶ (Rp_* ⋙ j_!) ⋙ (Lp'^* ⋙ Rp'_*)` obtained by inserting the unit of the adjunction
`Lp'^* ⊣ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep :
    boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⟶
      (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ p' ⋙ boundedConstructibleLowerStar Λ ℓ p') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p').unit

/-- The *square transport* step of the exchange morphism: `Functor.squareTransport` applied to
the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!` of the cartesian
square, under `Rp_*` on the left and `Rp'_*` on the right. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    (sq : IsPullback p i' j p') :
    (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ p' ⋙ boundedConstructibleLowerStar Λ ℓ p') ≅
      (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleUpperStar Λ ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
          boundedConstructibleLowerStar Λ ℓ p') :=
  Functor.squareTransport (boundedConstructibleLowerStar Λ ℓ p)
    (boundedConstructibleLowerStar Λ ℓ p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq)

/-- The *counit contraction* step of the exchange morphism: the natural transformation
`(Rp_* ⋙ Lp^*) ⋙ (i'_! ⋙ Rp'_*) ⟶ i'_! ⋙ Rp'_*` obtained by contracting the counit of the
adjunction `Lp^* ⊣ Rp_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep :
    (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleUpperStar Λ ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
          boundedConstructibleLowerStar Λ ℓ p') ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
        boundedConstructibleLowerStar Λ ℓ p' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The *exchange morphism* `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` on bounded constructible complexes for
a cartesian square
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` and `i'` open immersions: the mate, under the adjunctions `Lp^* ⊣ Rp_*` and
`Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!`
(`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`), assembled as the composite of the
unit insertion, the square transport, and the counit contraction:
`Rp_* ⋙ j_! ⟶ Rp_* ⋙ j_! ⋙ Lp'^* ⋙ Rp'_* ≅ Rp_* ⋙ Lp^* ⋙ i'_! ⋙ Rp'_* ⟶ i'_! ⋙ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
        boundedConstructibleLowerStar Λ ℓ p' :=
  boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep Λ ℓ ≫
    (boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep Λ ℓ sq).hom ≫
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep Λ ℓ


private lemma exchange_eq_mate (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange Λ ℓ sq =
      (mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p')
        (TwoSquare.mk _ _ _ _
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).hom)).natTrans := by
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
    [IsIso (boundedConstructibleBaseChange Λ ℓ sqc.toCommSq)] :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange Λ ℓ sq) := by
  have hj := boundedOpenUnitIsIso Λ ℓ j
  have hi' := boundedOpenUnitIsIso Λ ℓ i'
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
  have point (K : Dᵇc(X'.left)⟦Λ⟧) :
      IsIso ((boundedConstructibleLowerStarOpenImmersionLowerShriekExchange Λ ℓ sq).app K) := by
    let f := (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange Λ ℓ sq).app K
    have hopen : IsIso ((boundedConstructibleUpperStar Λ ℓ j).map f) := by
      dsimp only [f]
      rw [exchange_eq_mate]
      exact isIso_map_mateEquiv_app_of_isIso
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p')
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i')
        (TwoSquare.mk _ _ _ _
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).hom) K
    suffices hmap : IsIso ((boundedConstructible _).ι.map f) from
      isIso_of_reflects_iso f (boundedConstructible _).ι
    apply (derivedModuleJointIso Λ c.left j.left (by rw [hc]; simp)).isIso_of_pairFunctor
    · refine isIso_of_source_target_iso_zero _
        (derivedPullbackExtensionZero Λ j.left c.left hdisj
          ((boundedConstructibleLowerStar Λ ℓ p).obj K).obj).isoZero
        (IsZero.isoZero ?_)
      have hN : IsZero ((boundedConstructibleUpperStar Λ ℓ r).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i').obj K)) :=
        IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _
          (derivedPullbackExtensionZero Λ i'.left r.left hdisj' K.obj)
      have htarget : IsZero ((boundedConstructibleUpperStar Λ ℓ c).obj
          ((boundedConstructibleLowerStar Λ ℓ p').obj
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i').obj K))) :=
        ((boundedConstructibleLowerStar Λ ℓ q).map_isZero hN).of_iso
          (asIso ((boundedConstructibleBaseChange Λ ℓ sqc.toCommSq).app
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i').obj K)))
      exact (boundedConstructible _).ι.map_isZero htarget
    · exact (NatIso.isIso_map_iff
        (boundedConstructibleUpperStarCompatibility Λ ℓ j) f).1 (by
          change IsIso ((boundedConstructible _).ι.map
            ((boundedConstructibleUpperStar Λ ℓ j).map f))
          infer_instance)
  exact NatIso.isIso_of_isIso_app _

private theorem exchangeIsIsoOfProperBC
    [IsProper p'.left] (sq : IsPullback p i' j p')
    (hBC : ∀ {C P : Over (Spec (.of k))}
      [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
      [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
      (c : C ⟶ Z) (r : P ⟶ Z') (q : P ⟶ C) (sqc : IsPullback r q p' c),
      IsIso (boundedConstructibleBaseChange Λ ℓ sqc.toCommSq)) :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange Λ ℓ sq) := by
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
  exact exchangeIsIsoOfComplement Λ ℓ sq c r q sqc j.left.range_closedComplement

end Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section ExchangeIsIso

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]

/-- For bounded constructible `E`-sheaves, the exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of
a cartesian square with `p'` proper is an isomorphism: over the open `X ⊆ Z` it is the
identification `Lj^* ⋙ Rp'_* ≅ Rp_* ⋙ Li'^*`, and over the closed complement `Z ∖ X` the stalks
of `Rp'_*(i'_! K)` are, by proper base change, the cohomology of the fibres of `p'` over `Z ∖ X`,
which do not meet `X' ⊆ Z'`, with coefficients in `i'_! K`, hence vanish. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      (Profinite.continuousMapRingObj E) ℓ sq) := by
  apply exchangeIsIsoOfProperBC _ ℓ sq
  intro C P _ _ _ _ _ _ c r q sqc
  exact isIso_boundedConstructibleBaseChange_of_isProper ℓ E sqc

/-- For bounded constructible `ℚ̄_ℓ`-sheaves, the exchange morphism
`Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'` proper is an isomorphism. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl
    (sq : IsPullback p i' j p') :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      (Profinite.padicAlgClRingObj ℓ) ℓ sq) := by
  apply exchangeIsIsoOfProperBC _ ℓ sq
  intro C P _ _ _ _ _ _ c r q sqc
  exact isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sqc

end ExchangeIsIso

/-! ### The composition isomorphisms -/

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `E`-sheaves: for the chosen compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of
`f` and `c' = (Y ⟶[j] Z' ⟶[q] S)` of `g`, and a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')` of
`p ≫ j` with cartesian square (`Compactification.exists_isPullback_overG_overI`), the composite
of the independence of the compactification
(`boundedConstructibleLowerShriekOfCompactificationIso`) for the composite compactification
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S`, of the composition isomorphisms of `j_!` and `Rf_*`, and of the
inverse of the exchange isomorphism `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekComp_continuousMap :
    boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ f ⋙
        boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ g :=
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
    (boundedConstructibleLowerShriekRefinementIso _ ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp _ ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        _ ℓ hd.choose_spec)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `ℚ̄_ℓ`-sheaves, constructed as
`boundedConstructibleLowerShriekComp_continuousMap`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekComp_padicAlgCl :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ g :=
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
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ
    hd.choose_spec
  boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ _ (c.overComp c' d) ≪≫
    (boundedConstructibleLowerShriekRefinementIso _ ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp _ ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        _ ℓ hd.choose_spec)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for the exceptional inverse image on
bounded constructible `E`-sheaves: the conjugate of
`boundedConstructibleLowerShriekComp_continuousMap` under the adjunctions
`R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekComp_continuousMap :
    boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E) ℓ (f ≫ g) ≅
      boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E) ℓ g ⋙
        boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E) ℓ f :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ (f ≫ g))
    ((boundedConstructibleUpperShriekAdjunction _ ℓ f).comp
      (boundedConstructibleUpperShriekAdjunction _ ℓ g))
    (boundedConstructibleLowerShriekComp_continuousMap ℓ E f g).symm

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for the exceptional inverse image on
bounded constructible `ℚ̄_ℓ`-sheaves: the conjugate of
`boundedConstructibleLowerShriekComp_padicAlgCl` under the adjunctions
`R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekComp_padicAlgCl :
    boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g) ≅
      boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ g ⋙
        boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ (f ≫ g))
    ((boundedConstructibleUpperShriekAdjunction _ ℓ f).comp
      (boundedConstructibleUpperShriekAdjunction _ ℓ g))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).symm

end AlgebraicGeometry.ProEtale.CondensedRing
