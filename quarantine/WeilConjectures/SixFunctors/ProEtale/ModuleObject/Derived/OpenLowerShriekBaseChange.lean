/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import Sheaf.Paper.ProfinitePointPullback

/-!

# Extension by zero and base change on bounded constructible module objects

Let `Λ` be a commutative condensed ring. All schemes are separated and of finite type over a
field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all morphisms are morphisms of
`Over (Spec (.of k))`. This file compares the extension by zero `j_!` along open immersions on the
bounded constructible derived categories `Dᵇc(-)⟦Λ⟧` with pullbacks and pushforwards along a
commutative square
```
X' --g'--> X
|          |
j'         j
v          v
Z' --g---> Z
```
with `j` and `j'` open immersions.

* **Base change for extension by zero.** The canonical exchange morphism
  `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange'`) is an
  isomorphism for a cartesian square
  (`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange'`).
* **The exchange morphism.** For the inverse of this isomorphism, the mate under the adjunctions
  `Lg'^* ⊣ Rg'_*` and `Lg^* ⊣ Rg_*` is the *exchange morphism* `Rg'_* ⋙ j_! ⟶ j'_! ⋙ Rg_*`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'`, where
  the square is written `IsPullback p i' j p'`). For a cartesian square with `g` proper it is an
  isomorphism, for the coefficient rings `E̲` of a finite extension `E` of `ℚ_ℓ` and `ℚ̲̄_ℓ`: this
  is part (3) of the blueprint lemma `det-sf-comp-composition-interchange`, proved in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange`.

Both morphisms are the exchange morphisms `CategoryTheory.Adjunction.exchangeLeft` and
`CategoryTheory.Adjunction.exchangeRight` of the abstract mate calculus of
`WeilConjectures.CategoryTheory.Adjunction.ExchangeMate`
(`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft`
and `..._eq_exchangeRight` for the exchange morphism).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange'` and, for a
  cartesian square, its inverse
  `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'`.
- `ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'`: the
  exchange morphism `Rg'_* ⋙ j_! ⟶ j'_! ⋙ Rg_*`.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange'`: base
  change for extension by zero (blueprint `sk-def-sfb-open-base-change`).

-/

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- The cartesian sheaf comparison detects support; the module essential-image lemma
-- lifts support without requiring equality of the module and sheaf exchange maps.
private theorem cartesianModuleCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z X' Z' : Scheme.{u}}
    {j : X ⟶ Z} {g : Z' ⟶ Z} {j' : X' ⟶ Z'} {g' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback g' j' j g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ j').counit.app
      ((upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M))) := by
  let e := (profinitePointModuleForgetPullbackIso Λ g).app
      ((openImmersionLowerShriek Λ j).obj M) ≪≫
    ((ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1} sq).app M.X).symm
  apply (Adjunction.isIso_counit_app_iff_mem_essImage _).2
  apply mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ j'
  exact ⟨_, ⟨e.symm⟩⟩

-- Derive the invertible underived counit and use full faithfulness to detect the
-- derived counit on its essential image.
private theorem cartesianDerivedCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z X' Z' : Scheme.{u}}
    {j : X ⟶ Z} {g : Z' ⟶ Z} {j' : X' ⟶ Z'} {g' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback g' j' j g)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').counit.app
      ((D(openImmersionLowerShriek Λ j ⋙ upperStar Λ g)).obj K)) := by
  let F := openImmersionLowerShriek Λ j ⋙ upperStar Λ g
  let L := openImmersionLowerShriek Λ j'
  let R := upperStar Λ j'
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ j'
  have : IsIso adj.unit := Adjunction.unit_isIso_of_L_fully_faithful _
  have ff := adj.mapDerivedCategoryAdjunction.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let α : F ⋙ (R ⋙ L) ⟶ F :=
    Functor.whiskerLeft F adj.counit ≫ (Functor.rightUnitor F).hom
  have hαapp (M) : IsIso (α.app M) := by
    have : IsIso (adj.counit.app (F.obj M)) := cartesianModuleCounit Λ sq M
    dsimp only [α, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let e : D(F) ⋙ (D(R) ⋙ D(L)) ≅ D(F) :=
    Functor.isoWhiskerLeft D(F) (Functor.mapDerivedCategoryCompIso R L).symm ≪≫
      (Functor.mapDerivedCategoryCompIso F (R ⋙ L)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso α)
  exact adj.mapDerivedCategoryAdjunction.isIso_counit_app_of_iso (e.app K).symm

/-! ### Base change for extension by zero -/

section BaseChange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsFinitenessCoefficient ℓ Λ]

include ℓ k

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  (j : X ⟶ Z) (g : Z' ⟶ Z) (j' : X' ⟶ Z') (g' : X' ⟶ X)
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]



/-- The *unit insertion* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`Lg'^* ⋙ j'_! ⟶ (j_! ⋙ Lj^*) ⋙ (Lg'^* ⋙ j'_!)` obtained by inserting the unit of the adjunction
`j_! ⊣ Lj^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep' :
    boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' ⟶
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit
    (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')

variable {j g j' g'} in
/-- The *square transport* step of the extension-by-zero exchange morphism on bounded
constructible complexes: `Functor.squareTransport` applied to the pullback comparison
`Lj^* ∘ Lg'^* ≅ Lg^* ∘ Lj'^*` of the square, under `j_!` on the left and `j'_!` on the
right. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep'
    (sq : CommSq g' j' j g) :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') ≅
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ j' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') :=
  Functor.squareTransport (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq.flip)

/-- The *counit contraction* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`(j_! ⋙ Lg^*) ⋙ (Lj'^* ⋙ j'_!) ⟶ j_! ⋙ Lg^*` obtained by contracting the counit of the
adjunction `j'_! ⊣ Lj'^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep' :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ j' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g :=
  Functor.whiskerLeft
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').counit ≫
    (Functor.rightUnitor _).hom

variable {j g j' g'}

/-- The canonical exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` on bounded constructible
complexes for a commutative square
```
X' --g'--> X
|          |
j'         j
v          v
Z' --g---> Z
```
of schemes with `j` and `j'` open immersions, assembled as the composite of the unit insertion,
the square transport, and the counit contraction. -/
@[no_expose]
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChange' (sq : CommSq g' j' j g) :
    boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g :=
  boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep' Λ ℓ j j' g' ≫
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep' Λ ℓ sq).hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep' Λ ℓ j g j'

/-- The exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is the exchange morphism
`CategoryTheory.Adjunction.exchangeLeft` of the pullback comparison of the square under the
adjunctions `j_! ⊣ Lj^*` and `j'_! ⊣ Lj'^*`. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft
    (sq : CommSq g' j' j g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq.flip) := by
  unfold boundedConstructibleOpenImmersionLowerShriekBaseChange'
    boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep'
    boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep'
    boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep' Adjunction.exchangeLeft
  rfl

-- Transport through the ambient compatibility isomorphisms, then reflect the
-- restricted counit through the fully faithful bounded-constructible inclusion.
private theorem boundedCartesianCounit (sq : IsPullback g' j' j g)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    IsIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').counit.app
      ((boundedConstructibleUpperStar Λ ℓ g).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K))) := by
  let B := (boundedConstructibleUpperStar Λ ℓ g).obj
    ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K)
  let e : B.obj ≅ (D(openImmersionLowerShriek Λ j.left ⋙ upperStar Λ g.left)).obj K.obj :=
    (boundedConstructibleUpperStarCompatibility Λ ℓ g).app
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K) ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory Λ g.left).app _ ≪≫
      (D(upperStar Λ g.left)).mapIso
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).app K) ≪≫
      (Functor.mapDerivedCategoryCompIso
        (openImmersionLowerShriek Λ j.left) (upperStar Λ g.left)).symm.app K.obj
  have hder := cartesianDerivedCounit Λ sq.overLeft K.obj
  have hB : IsIso
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j'.left).counit.app B.obj) :=
    (NatTrans.isIso_app_iff_of_iso _ e).mpr hder
  let a := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j'.left).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j'.left).symm
  have hA : IsIso (a.counit.app B.obj) := by
    dsimp only [a]
    simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  have hm : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').counit.app
        B)) := by
    change IsIso ((boundedConstructible _).ι.map
      ((a.restrictFullyFaithful (ObjectProperty.fullyFaithfulι _)
        (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j').symm
        (boundedConstructibleUpperStarCompatibility Λ ℓ j').symm).counit.app B))
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    have : IsIso (a.counit.app ((boundedConstructible _).ι.obj B)) := hA
    infer_instance
  exact isIso_of_reflects_iso _ (boundedConstructible _).ι

/-- **Base change for extension by zero** on bounded constructible complexes: for a *cartesian*
square with `j` and `j'` open immersions, the exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is
an isomorphism.

Mathematically, since the square is cartesian, `X'` is the preimage of the open subscheme
`X ⊆ Z` under `g`, and on stalks at points of `Z'_proét` both sides are the pulled-back stalk at
points of `X'` and vanish outside `X'`. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' (sq : IsPullback g' j' j g) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq.toCommSq) := by
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
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
  have : IsIso (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have (K : ProEtale.BoundedConstructible (condensedRingObj Λ X.left)) :
      IsIso ((boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq.toCommSq).app K) := by
    have := boundedCartesianCounit Λ ℓ sq K
    dsimp only [boundedConstructibleOpenImmersionLowerShriekBaseChange',
      boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep',
      boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep',
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The extension-by-zero exchange isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!` on bounded
constructible complexes for a cartesian square of open immersions: the inverse of the canonical
exchange morphism, which is an isomorphism by base change for extension by zero. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
    (sq : IsPullback g' j' j g) :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g ≅
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq
  (asIso (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq.toCommSq)).symm

end BaseChange

/-! ### The exchange morphism -/

section Exchange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsFinitenessCoefficient ℓ Λ]
  {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

include ℓ k

/-- The *unit insertion* step of the exchange morphism: the natural transformation
`Rp_* ⋙ j_! ⟶ (Rp_* ⋙ j_!) ⋙ (Lp'^* ⋙ Rp'_*)` obtained by inserting the unit of the adjunction
`Lp'^* ⊣ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep'
    [IsFinitenessCoefficient ℓ Λ] :
    boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⟶
      (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ p' ⋙ boundedConstructibleLowerStar Λ ℓ p') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p').unit

/-- The *square transport* step of the exchange morphism: `Functor.squareTransport` applied to
the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!` of the cartesian
square, under `Rp_*` on the left and `Rp'_*` on the right. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep'
    [IsFinitenessCoefficient ℓ Λ]
    (sq : IsPullback p i' j p') :
    (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ p' ⋙ boundedConstructibleLowerStar Λ ℓ p') ≅
      (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleUpperStar Λ ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
          boundedConstructibleLowerStar Λ ℓ p') :=
  Functor.squareTransport (boundedConstructibleLowerStar Λ ℓ p)
    (boundedConstructibleLowerStar Λ ℓ p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq)

/-- The *counit contraction* step of the exchange morphism: the natural transformation
`(Rp_* ⋙ Lp^*) ⋙ (i'_! ⋙ Rp'_*) ⟶ i'_! ⋙ Rp'_*` obtained by contracting the counit of the
adjunction `Lp^* ⊣ Rp_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep'
    [IsFinitenessCoefficient ℓ Λ] :
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
(`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'`), assembled as the composite of the
unit insertion, the square transport, and the counit contraction:
`Rp_* ⋙ j_! ⟶ Rp_* ⋙ j_! ⋙ Lp'^* ⋙ Rp'_* ≅ Rp_* ⋙ Lp^* ⋙ i'_! ⋙ Rp'_* ⟶ i'_! ⋙ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    [IsFinitenessCoefficient ℓ Λ]
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
        boundedConstructibleLowerStar Λ ℓ p' :=
  boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep' Λ ℓ ≫
    (boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep' Λ ℓ sq).hom ≫
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep' Λ ℓ


/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the extension-by-zero base-change isomorphism under
the adjunctions `Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`. -/
lemma boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchangeRight
    [IsFinitenessCoefficient ℓ Λ]
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' Λ ℓ sq =
      Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p')
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq) := by
  unfold boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep'
    Adjunction.exchangeRight
  rfl

/-- The inverse of the extension-by-zero base-change isomorphism is the exchange morphism
`CategoryTheory.Adjunction.exchangeLeft` of the pullback comparison. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'_inv
    (sq : IsPullback p i' j p') :
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq).inv =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip) :=
  boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft Λ ℓ sq.toCommSq

end Exchange

end AlgebraicGeometry.ProEtale.CondensedRing
