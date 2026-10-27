/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.TraceFormula.SharpeningFanBijection
public import Mathlib.Geometry.RingedSpace.OpenImmersion

import Sheaf.GroupTheory.FineMonoidUnitSplitting
import Sheaf.AlgebraicGeometry.AffineFanLocalizationSections

/-!
# Synchronized descent from affine monoscheme lifts

Source: ILO VIII 3.1.4(iii), 3.1.11, 3.1.25--3.1.27, pp.98,100,102,
and Remark 2.3.5(ii)--(iii), p.92
(blueprint: lem-trf-affine-lift-tower-descent).

All local towers retain the length of the single tower on the disjoint union.
Uniqueness means the unique identification over the prescribed local towers.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Monoscheme

/-- Restriction of an ordered monoscheme tower to an affine component, without
contraction. The open-immersion and inverse-image equations specify the entire
restriction at each level, rather than just a commuting family of morphisms.
Source: ILO VIII 3.1.22--3.1.27, Remark 2.3.5(ii)
(blueprint: lem-trf-affine-lift-tower-descent). -/
structure AffineComponentRestriction {n : ℕ} (T : Tower.{u} n)
    (c : Chart (T.level 0).space) where
  tower : Tower.{u} n
  base : tower.level 0 = c.asFine
  pullback : PullbackTower T tower
  baseMap : (pullback.lift 0).map =
    eqToHom (congrArg Fine.space base) ≫ c.inclusion.map
  openImmersion : ∀ k : Fin (n + 1),
    SheafedSpace.IsOpenImmersion (pullback.lift k).map
  inverseImage : ∀ k : Fin n,
    Set.range (pullback.lift k.succ).map.hom.base =
      (T.arrow k).map.hom.base ⁻¹' Set.range (pullback.lift k.castSucc).map.hom.base
  torsionFree : c.asFine.IsTorsionFree
  sharpTorsionFree : (Fine.toFan c.asFine).IsTorsionFree
  sharpPullback : FineFan.PullbackTower T.toFan tower.toFan
  sharpMap : ∀ k : Fin (n + 1), (sharpPullback.lift k).map =
    (pullback.lift k).toFan.map

/-- The component chart transported to the actual zero level of a rule's tower.
This only transports along the rule's specified base equality.
Source: ILO VIII 3.1.26--3.1.27, Remark 2.3.5(ii)
(blueprint: lem-trf-affine-lift-tower-descent). -/
def AffineLiftCover.towerChart {F : FineFan.ResolutionInput.{u}}
    (C : AffineLiftCover F) (R : SmoothFunctorialDesingularization.{u})
    (i : Fin C.size) : Chart ((R.resolution C.total).tower.level 0).space :=
  (R.resolution C.total).base.symm ▸ C.monoChart i

/-- A globalization of the one tower on the disjoint union. Its maps are the
uncontracted recursive pullback, pinned to the given affine covering map.
The component maps are open immersions and jointly cover every level.
Source: ILO VIII 3.1.25--3.1.27, Remark 2.3.5(ii)
(blueprint: lem-trf-affine-lift-tower-descent). -/
structure AffineLiftTowerDescentData (R : SmoothFunctorialDesingularization.{u})
    (F : FineFan.ResolutionInput.{u}) (C : AffineLiftCover F) where
  tower : FineFan.Tower.{u} (R.resolution C.total).length
  base : tower.level 0 = F.fan
  pullback : FineFan.PullbackTower tower (R.resolution C.total).tower.toFan
  baseMap : (pullback.lift 0).map =
    eqToHom (congrArg (fun M : Fine.{u} ↦ (Fine.toFan M).space)
      (R.resolution C.total).base) ≫ C.map.map ≫
        eqToHom (congrArg FineFan.Fan.space base.symm)
  component : ∀ i : Fin C.size,
    AffineComponentRestriction (R.resolution C.total).tower (C.towerChart R i)
  componentOpen : ∀ (i : Fin C.size) (k : Fin ((R.resolution C.total).length + 1)),
    SheafedSpace.IsOpenImmersion
      (((component i).sharpPullback.lift k).map ≫ (pullback.lift k).map)
  cover : ∀ (k : Fin ((R.resolution C.total).length + 1)) (y : (tower.level k).space),
    ∃ (i : Fin C.size) (z : ((component i).tower.toFan.level k).space),
      (((component i).sharpPullback.lift k).map ≫ (pullback.lift k).map).hom.base z = y
  membership : ∀ (k : Fin (R.resolution C.total).length)
    (U : Opens (tower.level k.castSucc).space)
    (s : (tower.level k.castSucc).space.presheaf.obj (op U)),
    s ∈ tower.center k U ↔ ∀ i : Fin C.size,
      ((((component i).sharpPullback.lift k.castSucc).map ≫
        (pullback.lift k.castSucc).map).hom.c.app (op U)) s ∈
          (component i).tower.toFan.center k
            ((Opens.map ((((component i).sharpPullback.lift k.castSucc).map ≫
              (pullback.lift k.castSucc).map).hom.base)).obj U)
  finiteCover : ∀ k : Fin ((R.resolution C.total).length + 1),
    (tower.level k).HasFiniteAffineCover
  smooth : (tower.level (Fin.last (R.resolution C.total).length)).IsSmooth
  contracted : ∀ k : Fin (R.resolution C.total).length,
    ¬ (tower.center k = FineFan.wholeIdeal (tower.level k.castSucc) ∧
      IsIso (tower.arrow k).map)

/-- The prescribed identification between two globalizations: it commutes with
all the maps from the single original sharpened tower. This pins it to the
identity on common centers and on their localized fraction generators.
Source: ILO VIII 3.1.25--3.1.27 and blowup rigidity preceding Remark 2.3.5
(blueprint: lem-trf-affine-lift-tower-descent). -/
def IsAffineDescentIdentification {R : SmoothFunctorialDesingularization.{u}}
    {F : FineFan.ResolutionInput.{u}} {C : AffineLiftCover F}
    (D E : AffineLiftTowerDescentData R F C)
    (c : FineFan.TowerIdentification D.tower E.tower) : Prop :=
  (∃ h : ∀ k, c.index k = k,
    ∀ k : Fin ((R.resolution C.total).length + 1),
      (D.pullback.lift k).map ≫ (c.iso k).hom =
        (E.pullback.lift k).map ≫
          eqToHom (congrArg (fun j ↦ (E.tower.level j).space) (h k).symm))

/-- The chart prime corresponding to an actual point of the fan.
Source: ILO VIII 3.1.3--3.1.4 (blueprint: lem-trf-affine-lift-tower-descent). -/
noncomputable def chartPrime {F : FineFan.Fan.{u}} (c : FineFan.Chart F.space)
    (x : F.space) (hx : x ∈ c.openSet) : FineFan.MonoidPrime c.monoid :=
  c.iso.hom.hom.base ⟨x, hx⟩

/-- The additive sum in the node is a product in the multiplicative convention.
It uses precisely the chosen generators outside the prime, including the empty product.
Source: ILO VIII 3.1.4(iii) (blueprint: lem-trf-affine-lift-tower-descent). -/
noncomputable def neighborhoodGenerator {P : Type u} [CommMonoid P]
    (r : ℕ) (e : Fin r → P) (x : FineFan.MonoidPrime P) : P := by
  classical
  exact (Finset.univ.filter (fun i ↦ e i ∉ x.carrier)).prod e

/-- The actual numerator homomorphism into the localization inside the completion.
Source: ILO VIII 3.1.2 (blueprint: lem-trf-affine-lift-tower-descent). -/
def localizationNumerator (P : Type u) [CommMonoid P] (a : P) :
    P →* Algebra.faceLocalization P (Submonoid.powers a) where
  toFun p := ⟨Algebra.GrothendieckGroup.of p, p, 1, by simp⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' p q := Subtype.ext (map_mul _ p q)

/-- The smallest overlap neighborhood with its canonical section-to-stalk map.
The local charts are the unsharp localizations, with their numerator maps fixed.
Source: ILO VIII 3.1.4(iii), 3.1.11, pp.98--100
(blueprint: lem-trf-affine-lift-tower-descent). -/
structure AffineOverlapNeighborhood {F : FineFan.ResolutionInput.{u}}
    (C : AffineLiftCover F) (i j : Fin C.size) (x : F.fan.space) where
  openSet : Opens F.fan.space
  contains : x ∈ openSet
  generalizations : ∀ y : F.fan.space, y ∈ openSet ↔ y ⤳ x
  smallest : ∀ U : Opens F.fan.space, x ∈ U → openSet ≤ U
  inCharts : openSet ≤ (C.fanChart i).openSet ⊓ (C.fanChart j).openSet
  chart : FineFan.Chart F.fan.space
  chartOpen : chart.openSet = openSet
  chartMonoid : chart.monoid = FineFan.stalk F.fan.space.presheaf x
  germBijective : Function.Bijective (FineFan.germ F.fan.space.presheaf openSet x contains)
  localChart : ∀ (l : Fin C.size), x ∈ (C.fanChart l).openSet →
    Chart C.total.monoscheme.space
  localOpen : ∀ (l : Fin C.size) (hl : x ∈ (C.fanChart l).openSet),
    (localChart l hl).openSet = (C.monoChart l).openSet ⊓
      (Opens.map C.map.map.hom.base).obj openSet
  principal : ∀ (l : Fin C.size) (hl : x ∈ (C.fanChart l).openSet)
    (r : ℕ) (e : Fin r → (C.fanChart l).monoid),
    Submonoid.closure (Set.range e) = ⊤ →
      (openSet : Set F.fan.space) =
        (fun y ↦ (SheafedSpace.ofRestrict F.fan.space
          (C.fanChart l).openSet.isOpenEmbedding).hom.base
            ((C.fanChart l).iso.inv.hom.base y)) ''
              (FineFan.basicOpen (neighborhoodGenerator r e
                (chartPrime (C.fanChart l) x hl))).1
  localization : ∀ (l : Fin C.size) (hl : x ∈ (C.fanChart l).openSet)
    (r : ℕ) (e : Fin r → (C.fanChart l).monoid),
    Submonoid.closure (Set.range e) = ⊤ →
      ∃ f : (localChart l hl).monoid ≃*
          Algebra.faceLocalization (C.fanChart l).monoid
            (Submonoid.powers (neighborhoodGenerator r e
              (chartPrime (C.fanChart l) x hl))),
        ∃ g : affine (localChart l hl).monoid ⟶ affine (C.fanChart l).monoid,
          IsAffineMap (f.symm.toMonoidHom.comp
            (localizationNumerator (C.fanChart l).monoid
              (neighborhoodGenerator r e (chartPrime (C.fanChart l) x hl)))) g ∧
          (localChart l hl).iso.inv ≫ (localChart l hl).inclusion.map =
            g ≫ eqToHom (congrArg (fun P : CommMonCat.{u} ↦ affine P) (C.sameMonoid l).symm) ≫
              (C.monoChart l).iso.inv ≫ (C.monoChart l).inclusion.map

/-- A splitting supplies the section b ↦ (b,1), the map of monoids inducing
its sharp quotient chart. Source: ILO VIII 3.1.11
(blueprint: lem-trf-affine-lift-tower-descent). -/
def splittingSection {A : Type u} {B : Type v} {G : Type w}
    [CommMonoid A] [CommMonoid B] [CommMonoid G]
    (e : A ≃* (B × G)) : B →* A where
  toFun b := e.symm (b, 1)
  map_one' := by simp
  map_mul' b c := by simpa using e.symm.map_mul (b, 1) (c, 1)

/-- A unit splitting of a local model over the intrinsic sharp overlap chart.
The square fixes the quotient to the identity of the given fan neighborhood.
Source: ILO VIII 3.1.11, 3.1.25--3.1.27
(blueprint: lem-trf-affine-lift-tower-descent). -/
structure AffineOverlapSplitting {F : FineFan.ResolutionInput.{u}}
    {C : AffineLiftCover F} {i j : Fin C.size} {x : F.fan.space}
    (N : AffineOverlapNeighborhood C i j x) (l : Fin C.size)
    (hl : x ∈ (C.fanChart l).openSet) where
  rank : ℕ
  split : (N.localChart l hl).monoid ≃*
    (N.chart.monoid × Multiplicative (Fin rank → ℤ))
  quotient : FineFan.affine (N.localChart l hl).monoid ⟶ FineFan.affine N.chart.monoid
  canonical : FineFan.IsAffineMap
    (splittingSection split) quotient
  overFan : quotient ≫ N.chart.iso.inv ≫
      SheafedSpace.ofRestrict F.fan.space N.chart.openSet.isOpenEmbedding =
    sharpSpaceMap
      (N := affineFine (N.localChart l hl).monoid (N.localChart l hl).fine)
      (M := (N.localChart l hl).asFine) (N.localChart l hl).iso.inv ≫
      (N.localChart l hl).inclusion.toFan.map ≫ C.map.map

/-- Inclusion of the first unsharp model into the common product, on monoids.
Source: ILO VIII 3.1.11, 3.1.27 (blueprint: lem-trf-affine-lift-tower-descent). -/
def commonLiftLeft {A B : Type u} [CommMonoid A] [CommMonoid B] (s t : ℕ)
    (e : A ≃* (B × Multiplicative (Fin s → ℤ))) :
    A →* (B × Multiplicative (Fin s → ℤ) × Multiplicative (Fin t → ℤ)) where
  toFun a := ((e a).1, (e a).2, 1)
  map_one' := by simp
  map_mul' a b := by simp

/-- Inclusion of the second unsharp model into the common product, on monoids.
Source: ILO VIII 3.1.11, 3.1.27 (blueprint: lem-trf-affine-lift-tower-descent). -/
def commonLiftRight {A B : Type u} [CommMonoid A] [CommMonoid B] (s t : ℕ)
    (e : A ≃* (B × Multiplicative (Fin t → ℤ))) :
    A →* (B × Multiplicative (Fin s → ℤ) × Multiplicative (Fin t → ℤ)) where
  toFun a := ((e a).1, 1, (e a).2)
  map_one' := by simp
  map_mul' a b := by simp

/-- The explicit product lift of two split overlap models. Both maps are fixed
by the inclusions of monoids and are smooth and surjective. The towers are full
recursive pullbacks of the same original tower, with unique comparison over V.
After sharpening that comparison is the identity on the descended local models.
Source: ILO VIII 3.1.11, 3.1.25--3.1.27 and Remark 2.3.5(iii)
(blueprint: lem-trf-affine-lift-tower-descent). -/
structure AffineOverlapCommonLift {R : SmoothFunctorialDesingularization.{u}}
    {F : FineFan.ResolutionInput.{u}} {C : AffineLiftCover F}
    (D : AffineLiftTowerDescentData R F C) {i j : Fin C.size} {x : F.fan.space}
    (N : AffineOverlapNeighborhood C i j x)
    (hi : x ∈ (C.fanChart i).openSet) (hj : x ∈ (C.fanChart j).openSet)
    (S : AffineOverlapSplitting N i hi) (S' : AffineOverlapSplitting N j hj) where
  input : ResolutionInput.{u}
  affineIso : input.monoscheme.space ≅
    affine (N.chart.monoid × Multiplicative (Fin S.rank → ℤ) ×
      Multiplicative (Fin S'.rank → ℤ))
  left : Hom input.monoscheme (N.localChart i hi).asFine
  right : Hom input.monoscheme (N.localChart j hj).asFine
  leftCanonical : IsAffineMap (commonLiftLeft S.rank S'.rank S.split)
    (affineIso.inv ≫ left.map ≫ (N.localChart i hi).iso.hom)
  rightCanonical : IsAffineMap (commonLiftRight S.rank S'.rank S'.split)
    (affineIso.inv ≫ right.map ≫ (N.localChart j hj).iso.hom)
  leftSmooth : left.IsSmooth
  rightSmooth : right.IsSmooth
  leftSurjective : Function.Surjective left.map.hom.base
  rightSurjective : Function.Surjective right.map.hom.base
  leftToTotal : Hom input.monoscheme C.total.monoscheme
  rightToTotal : Hom input.monoscheme C.total.monoscheme
  leftComposite : leftToTotal.map = left.map ≫ (N.localChart i hi).inclusion.map
  rightComposite : rightToTotal.map = right.map ≫ (N.localChart j hj).inclusion.map
  leftTotalSmooth : leftToTotal.IsSmooth
  rightTotalSmooth : rightToTotal.IsSmooth
  sharpComposite : leftToTotal.toFan.map ≫ C.map.map =
    rightToTotal.toFan.map ≫ C.map.map
  leftTower : Tower.{u} (R.resolution C.total).length
  rightTower : Tower.{u} (R.resolution C.total).length
  leftBase : leftTower.level 0 = input.monoscheme
  rightBase : rightTower.level 0 = input.monoscheme
  leftPullback : PullbackTower (R.resolution C.total).tower leftTower
  rightPullback : PullbackTower (R.resolution C.total).tower rightTower
  leftBaseMap : (leftPullback.lift 0).map =
    eqToHom (congrArg Fine.space leftBase) ≫ leftToTotal.map ≫
      eqToHom (congrArg Fine.space (R.resolution C.total).base.symm)
  rightBaseMap : (rightPullback.lift 0).map =
    eqToHom (congrArg Fine.space rightBase) ≫ rightToTotal.map ≫
      eqToHom (congrArg Fine.space (R.resolution C.total).base.symm)
  comparison : TowerIdentification leftTower rightTower
  sameIndex : ∀ k, comparison.index k = k
  baseComparison : (comparison.iso 0).hom =
    eqToHom (congrArg Fine.space (leftBase.trans rightBase.symm)) ≫
      eqToHom (congrArg (fun k ↦ (rightTower.level k).space) (sameIndex 0).symm)
  unique : ∀ (c : TowerIdentification leftTower rightTower)
    (h : ∀ k, c.index k = k),
    (c.iso 0).hom =
      eqToHom (congrArg Fine.space (leftBase.trans rightBase.symm)) ≫
        eqToHom (congrArg (fun k ↦ (rightTower.level k).space) (h 0).symm) →
      c = comparison
  sharpComparison : ∀ k : Fin ((R.resolution C.total).length + 1),
    (leftPullback.lift k).toFan.map ≫ (D.pullback.lift k).map =
      sharpSpaceMap (N := leftTower.level k) (M := rightTower.level (comparison.index k))
        (comparison.iso k).hom ≫
        eqToHom (congrArg (fun l ↦ (Fine.toFan (rightTower.level l)).space)
          (sameIndex k)) ≫
            (rightPullback.lift k).toFan.map ≫ (D.pullback.lift k).map

/-- Synchronized affine lifts descend uniquely, retaining all original stages.
The overlap and common-lift data specify the intrinsic smallest neighborhoods,
canonical fractions, and the identity comparison on every pulled-back center.
The global object has the membership-defined centers and their saturated blowups;
uniqueness over the component maps makes these comparisons satisfy the cocycle law.
Source: ILO VIII 3.1.4(iii), 3.1.11, 3.1.25--3.1.27, pp.98,100,102,
and Remark 2.3.5(ii)--(iii), p.92
(blueprint: lem-trf-affine-lift-tower-descent).

Proof:
1. Each sharp chart monoid has torsion-free completion, by its closed-point stalk.
   Localization preserves this completion, and sharpening gives the fan stalks.
   Thus the affine lifts and their finite disjoint union belong to the rule domain.
   Restrict the single tower R(L) without contraction and sharpen it, using
   lem-trf-sharpening-blowup-chart-comparison.
2. By lem-trf-monoid-prime-minimal-neighborhood, the generators outside the prime
   give the smallest open D(a), intrinsically the generalizations of x. It lies
   in both charts. By lem-trf-affine-fan-localization-sections, its sharp sections
   and its stalk are B; the unsharp sections are the displayed localizations.
3. Apply lem-trf-fine-monoid-unit-splitting to the two localizations. Given their
   splittings, form B times both free unit groups. Its primes are precisely the
   inverse images of primes of B; hence the two projection-induced spectrum maps
   are surjective. Their stalks append a free unit group, proving smoothness.
   Both torsion-free conditions hold on the common product lift.
4. Apply lem-trf-smooth-tower-index-synchronization to the two composites V to L.
   The disjoint-union trick with V disjoint union L identifies the complete
   uncontracted pullbacks, with every original center and index.
5. Sharpen this identification by lem-trf-sharpening-blowup-chart-comparison.
   It fixes the common sharp sections and the adjoined fractions b/a. Thus it is
   independent of splittings; on smaller overlaps the maps still fix all these
   generators. Three comparisons therefore satisfy the cocycle equation.
6. Define the first ideal by membership in every local ideal after restriction.
   Agreement on overlaps proves it is an ideal subsheaf and restricts to each
   given ideal. The local finite nonempty generators prove coherence and
   nonemptiness; sheaf locality proves uniqueness of this membership rule.
7. Form its saturated blowup using def-trf-fine-fan-blowup. Its fraction charts
   and transitions are exactly the local ones, so they glue by the specified
   identities. This constructs the next level and its covering maps.
8. Repeat steps 6 and 7 at each original index. Induction produces all n levels,
   their finite affine covers, and the center membership formula at every level.
   The same induction and fraction-chart rigidity give the unique identification
   between any two descents, fixing the maps from the original component towers.
9. Final smoothness is local on the component cover and is reflected by
   sharpening, by lem-trf-smooth-tower-index-synchronization. A globally removable
   stage would be removable on every component, hence in R(L), contradicting
   that lemma's contractedness. Local identity stages are retained.
10. If the fan is empty, L is empty. Every potential stage has whole ideal and
    isomorphism arrow, so contractedness forces n = 0. This includes the empty
    cover. For n = 0 on a nonempty fan all center assertions are vacuous. -/
theorem affine_lift_tower_descent (R : SmoothFunctorialDesingularization.{u})
    (F : FineFan.ResolutionInput.{u}) (C : AffineLiftCover F) :
    ∃ D : AffineLiftTowerDescentData R F C,
      (∀ E : AffineLiftTowerDescentData R F C,
        ∃! c : FineFan.TowerIdentification D.tower E.tower,
          IsAffineDescentIdentification D E c) ∧
      (∀ (i j : Fin C.size) (x : F.fan.space)
        (hi : x ∈ (C.fanChart i).openSet) (hj : x ∈ (C.fanChart j).openSet),
        ∃ N : AffineOverlapNeighborhood C i j x,
          ∀ (S : AffineOverlapSplitting N i hi) (S' : AffineOverlapSplitting N j hj),
            Nonempty (AffineOverlapCommonLift D N hi hj S S')) ∧
      (IsEmpty F.fan.space → (R.resolution C.total).length = 0) := by
  sorry

end AlgebraicGeometry.Monoscheme
