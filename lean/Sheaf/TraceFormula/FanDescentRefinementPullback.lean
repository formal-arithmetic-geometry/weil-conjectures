/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.AffineLiftTowerDescent
public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Sheaf.AlgebraicGeometry.FineFanBlowup

import Sheaf.AlgebraicGeometry.AffineFanHomUniversal
import Sheaf.AlgebraicGeometry.AffineFanLocalizationSections
import Sheaf.GroupTheory.FineMonoidUnitSplitting

/-!
# Cover refinements and smooth pullback of descended fan towers

Source: ILO VIII 3.1.13--3.1.16, 3.1.22, 3.1.25--3.1.27, pp.100--102,
and Remark 2.3.5(ii)--(iii), p.92
(blueprint: lem-trf-fan-descent-refinement-pullback).

The auxiliary structures unpack the comparisons asserted by this node. All towers,
centers, recursive pullbacks and contractions are the existing geometric definitions.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Monoscheme

/-- A tower identification over the identity of its given fan base.
Source: ILO VIII 3.1.25--3.1.27, Remark 2.3.5(ii)
(blueprint: lem-trf-fan-descent-refinement-pullback). -/
def IsBasedFanTowerIdentification {n m : ℕ} {F : FineFan.Fan.{u}}
    {T : FineFan.Tower.{u} n} {S : FineFan.Tower.{u} m}
    (bT : T.level 0 = F) (bS : S.level 0 = F)
    (c : FineFan.TowerIdentification T S) : Prop :=
  (c.iso 0).hom = eqToHom (congrArg FineFan.Fan.space (bT.trans bS.symm)) ≫
    eqToHom (congrArg (fun j ↦ (S.level j).space) c.first.symm)

/-- Two lifted covers inside their combined finite disjoint union. The partition
of chart indices and the equations on the open chart inclusions fix the union maps.
Source: ILO VIII 3.1.26--3.1.27, Remark 2.3.5(ii)
(blueprint: lem-trf-fan-descent-refinement-pullback). -/
structure CombinedAffineLiftCover {F : FineFan.ResolutionInput.{u}}
    (C E : AffineLiftCover F) where
  cover : AffineLiftCover F
  partition : (Fin C.size ⊕ Fin E.size) ≃ Fin cover.size
  left : Hom C.total.monoscheme cover.total.monoscheme
  right : Hom E.total.monoscheme cover.total.monoscheme
  leftSmooth : left.IsSmooth
  rightSmooth : right.IsSmooth
  leftOpen : SheafedSpace.IsOpenImmersion left.map
  rightOpen : SheafedSpace.IsOpenImmersion right.map
  disjoint : Disjoint (Set.range left.map.hom.base) (Set.range right.map.hom.base)
  covers : Set.range left.map.hom.base ∪ Set.range right.map.hom.base = Set.univ
  leftOver : left.toFan.map ≫ cover.map.map = C.map.map
  rightOver : right.toFan.map ≫ cover.map.map = E.map.map
  leftChart : ∀ i : Fin C.size,
    Set.range (((C.monoChart i).inclusion.map ≫ left.map).hom.base) =
      (cover.monoChart (partition (.inl i))).openSet
  rightChart : ∀ i : Fin E.size,
    Set.range (((E.monoChart i).inclusion.map ≫ right.map).hom.base) =
      (cover.monoChart (partition (.inr i))).openSet

/-- Compatibility of restriction from one lifted cover to another with the
canonical map to the assigned fan tower. It records both the inherited index and
its map; the rule's own comparison supplies the contracted subunion restriction.
Source: ILO VIII 3.1.26--3.1.27, Remark 2.3.5(ii)--(iii)
(blueprint: lem-trf-fan-descent-refinement-pullback). -/
def IsFanSubcoverCompatibility (R : SmoothFunctorialDesingularization.{u})
    (Q : FineFan.SmoothFunctorialDesingularization.{u})
    {F : FineFan.ResolutionInput.{u}} {C E : AffineLiftCover F}
    (D : AffineLiftTowerDescentData R F C) (B : AffineLiftTowerDescentData R F E)
    (c : FineFan.TowerIdentification D.tower (Q.resolution F).tower)
    (b : FineFan.TowerIdentification B.tower (Q.resolution F).tower)
    (j : Hom C.total.monoscheme E.total.monoscheme) (hj : j.IsSmooth) : Prop :=
  ∃ h : ∀ k : Fin ((R.resolution E.total).length + 1),
    b.index k = c.index ((R.comparison j hj).contraction.index k),
    ∀ k : Fin ((R.resolution E.total).length + 1),
      sharpSpaceMap ((R.comparison j hj).levelMap k) ≫
          (B.pullback.lift k).map ≫ (b.iso k).hom =
        (D.pullback.lift ((R.comparison j hj).contraction.index k)).map ≫
          (c.iso ((R.comparison j hj).contraction.index k)).hom ≫
            eqToHom (congrArg (fun l ↦ ((Q.resolution F).tower.level l).space)
              (h k).symm)

/-- The first-factor inclusion giving a smooth sharp affine model.
Source: ILO VIII 3.1.13--3.1.16
(blueprint: lem-trf-fan-descent-refinement-pullback). -/
def smoothFanModelInclusion {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (r : ℕ) (e : (P × Multiplicative (Fin r → ℕ)) ≃* Q) : P →* Q where
  toFun p := e (p, 1)
  map_one' := e.map_one
  map_mul' p q := e.map_mul (p, 1) (q, 1)

/-- The smallest source and target neighborhoods of a smooth fan map, with its
actual sharp affine monoscheme lift. At every prime its unsharp stalk map has
free ranks r-t and t, so smoothness is asserted everywhere on the model.
Source: ILO VIII 3.1.13--3.1.16, p.100
(blueprint: lem-trf-fan-descent-refinement-pullback). -/
structure SmoothFanNeighborhoodModel {F G : FineFan.ResolutionInput.{u}}
    (g : FineFan.Hom G.fan F.fan) (y : G.fan.space) where
  target : FineFan.Chart F.fan.space
  source : FineFan.Chart G.fan.space
  targetContains : g.map.hom.base y ∈ target.openSet
  sourceContains : y ∈ source.openSet
  targetSmallest : ∀ x : F.fan.space,
    x ∈ target.openSet ↔ x ⤳ g.map.hom.base y
  sourceSmallest : ∀ z : G.fan.space, z ∈ source.openSet ↔ z ⤳ y
  targetSharp : FineFan.IsSharp target.monoid
  sourceSharp : FineFan.IsSharp source.monoid
  targetStalk : target.monoid ≃* FineFan.stalk F.fan.space.presheaf (g.map.hom.base y)
  targetGermBijective : Function.Bijective
    (FineFan.germ F.fan.space.presheaf target.openSet (g.map.hom.base y) targetContains)
  sourceGermBijective : Function.Bijective
    (FineFan.germ G.fan.space.presheaf source.openSet y sourceContains)
  rank : ℕ
  product : (target.monoid × Multiplicative (Fin rank → ℕ)) ≃* source.monoid
  lift : Hom (affineFine source.monoid source.fine)
    (affineFine target.monoid target.fine)
  canonical : IsAffineMap (smoothFanModelInclusion rank product) lift.map
  smooth : lift.IsSmooth
  overFan : sharpSpaceMap lift.map ≫ target.iso.inv ≫
      SheafedSpace.ofRestrict F.fan.space target.openSet.isOpenEmbedding =
    source.iso.inv ≫ SheafedSpace.ofRestrict G.fan.space source.openSet.isOpenEmbedding ≫
      g.map
  localized : ∀ z : affine source.monoid, ∃ t : ℕ, t ≤ rank ∧
    ∃ e : (FineFan.stalk (affine target.monoid).presheaf (lift.map.hom.base z) ×
        Multiplicative (Fin (rank - t) → ℕ) × Multiplicative (Fin t → ℤ)) ≃*
          FineFan.stalk (affine source.monoid).presheaf z,
      ∀ p, e (p, 1, 1) = FineFan.stalkMap lift.map z p

/-- A single disjoint union synchronizing source and target affine covers of a
smooth fan map. These are the actual subunion open inclusions, before contraction.
Source: ILO VIII 3.1.26--3.1.27, Remark 2.3.5(ii)--(iii)
(blueprint: lem-trf-fan-descent-refinement-pullback). -/
structure SmoothCoverUnion {F G : FineFan.ResolutionInput.{u}}
    (g : FineFan.Hom G.fan F.fan) (C : AffineLiftCover F) (E : AffineLiftCover G) where
  total : ResolutionInput.{u}
  target : Hom C.total.monoscheme total.monoscheme
  source : Hom E.total.monoscheme total.monoscheme
  targetSmooth : target.IsSmooth
  sourceSmooth : source.IsSmooth
  targetOpen : SheafedSpace.IsOpenImmersion target.map
  sourceOpen : SheafedSpace.IsOpenImmersion source.map
  disjoint : Disjoint (Set.range target.map.hom.base) (Set.range source.map.hom.base)
  covers : Set.range target.map.hom.base ∪ Set.range source.map.hom.base = Set.univ
  models : ∀ y : G.fan.space, ∃ (i : Fin C.size) (j : Fin E.size)
    (M : SmoothFanNeighborhoodModel g y),
    M.target = C.fanChart i ∧ M.source = E.fanChart j

/-- Descent of the full restriction of the one tower on a larger disjoint union.
The restriction is precisely the pulled tower in R's comparison for the inclusion;
no index has yet been removed. Its sharpening descends over the original fan cover.
Source: ILO VIII 3.1.22, 3.1.25--3.1.27, Remark 2.3.5(ii)
(blueprint: lem-trf-fan-descent-refinement-pullback). -/
structure SubunionFanTower (R : SmoothFunctorialDesingularization.{u})
    {F : FineFan.ResolutionInput.{u}} (C : AffineLiftCover F)
    (J : ResolutionInput.{u}) (j : Hom C.total.monoscheme J.monoscheme)
    (hj : j.IsSmooth) where
  tower : FineFan.Tower.{u} (R.resolution J).length
  base : tower.level 0 = F.fan
  pullback : FineFan.PullbackTower tower (R.comparison j hj).pulled.toFan
  baseMap : (pullback.lift 0).map =
    eqToHom (congrArg (fun M : Fine.{u} ↦ (Fine.toFan M).space)
      (R.comparison j hj).base) ≫ C.map.map ≫
        eqToHom (congrArg FineFan.Fan.space base.symm)
  openImmersion : ∀ k : Fin ((R.resolution J).length + 1),
    SheafedSpace.IsOpenImmersion ((R.comparison j hj).pullback.lift k).map
  inverseImage : ∀ k : Fin (R.resolution J).length,
    Set.range ((R.comparison j hj).pullback.lift k.succ).map.hom.base =
      ((R.resolution J).tower.arrow k).map.hom.base ⁻¹'
        Set.range ((R.comparison j hj).pullback.lift k.castSucc).map.hom.base
  locallyOpen : ∀ (k : Fin ((R.resolution J).length + 1))
    (z : ((R.comparison j hj).pulled.toFan.level k).space),
    ∃ V : Opens ((R.comparison j hj).pulled.toFan.level k).space, z ∈ V ∧
      SheafedSpace.IsOpenImmersion
        (SheafedSpace.ofRestrict ((R.comparison j hj).pulled.toFan.level k).space
          V.isOpenEmbedding ≫ (pullback.lift k).map)
  cover : ∀ (k : Fin ((R.resolution J).length + 1)) (x : (tower.level k).space),
    ∃ z : ((R.comparison j hj).pulled.toFan.level k).space,
      (pullback.lift k).map.hom.base z = x

/-- The complete refinement and smooth-pullback conclusions for the tower obtained
from a monoscheme rule. The supplied fan rule is the cover-independent T_R.
The based uniqueness and cocycle fields fix canonical comparisons, including for
further refinements. Contraction data use the actual whole-ideal/isomorphism test.
Source: ILO VIII 3.1.13--3.1.16, 3.1.22, 3.1.25--3.1.27, Remark 2.3.5(ii)--(iii)
(blueprint: lem-trf-fan-descent-refinement-pullback). -/
structure FanDescentRefinementData (R : SmoothFunctorialDesingularization.{u})
    (Q : FineFan.SmoothFunctorialDesingularization.{u}) where
  descent : ∀ (F : FineFan.ResolutionInput.{u}) (C : AffineLiftCover F),
    AffineLiftTowerDescentData R F C
  toAssigned : ∀ (F : FineFan.ResolutionInput.{u}) (C : AffineLiftCover F),
    FineFan.TowerIdentification (descent F C).tower (Q.resolution F).tower
  based : ∀ (F : FineFan.ResolutionInput.{u}) (C : AffineLiftCover F),
    IsBasedFanTowerIdentification (descent F C).base (Q.resolution F).base (toAssigned F C)
  uniqueAssigned : ∀ (F : FineFan.ResolutionInput.{u}) (C : AffineLiftCover F)
    (c : FineFan.TowerIdentification (descent F C).tower (Q.resolution F).tower),
    IsBasedFanTowerIdentification (descent F C).base (Q.resolution F).base c →
      c = toAssigned F C
  compare : ∀ (F : FineFan.ResolutionInput.{u}) (C E : AffineLiftCover F),
    FineFan.TowerIdentification (descent F C).tower (descent F E).tower
  compareBased : ∀ (F : FineFan.ResolutionInput.{u}) (C E : AffineLiftCover F),
    IsBasedFanTowerIdentification (descent F C).base (descent F E).base (compare F C E)
  compareUnique : ∀ (F : FineFan.ResolutionInput.{u}) (C E : AffineLiftCover F)
    (c : FineFan.TowerIdentification (descent F C).tower (descent F E).tower),
    IsBasedFanTowerIdentification (descent F C).base (descent F E).base c → c = compare F C E
  compareIndex : ∀ (F : FineFan.ResolutionInput.{u}) (C E : AffineLiftCover F)
    (i : Fin ((R.resolution C.total).length + 1)),
    (toAssigned F E).index ((compare F C E).index i) = (toAssigned F C).index i
  compareMap : ∀ (F : FineFan.ResolutionInput.{u}) (C E : AffineLiftCover F)
    (i : Fin ((R.resolution C.total).length + 1)),
    ((compare F C E).iso i).hom ≫
        ((toAssigned F E).iso ((compare F C E).index i)).hom =
      ((toAssigned F C).iso i).hom ≫
        eqToHom (congrArg (fun j ↦ ((Q.resolution F).tower.level j).space)
          (compareIndex F C E i).symm)
  cocycleIndex : ∀ (F : FineFan.ResolutionInput.{u}) (C E A : AffineLiftCover F)
    (i : Fin ((R.resolution C.total).length + 1)),
    (compare F C A).index i = (compare F E A).index ((compare F C E).index i)
  cocycleMap : ∀ (F : FineFan.ResolutionInput.{u}) (C E A : AffineLiftCover F)
    (i : Fin ((R.resolution C.total).length + 1)),
    ((compare F C E).iso i).hom ≫
        ((compare F E A).iso ((compare F C E).index i)).hom =
      ((compare F C A).iso i).hom ≫
        eqToHom (congrArg (fun j ↦ ((descent F A).tower.level j).space)
          (cocycleIndex F C E A i))
  combined : ∀ (F : FineFan.ResolutionInput.{u}) (C E : AffineLiftCover F),
    ∃ U : CombinedAffineLiftCover C E,
      IsFanSubcoverCompatibility R Q (descent F C) (descent F U.cover)
        (toAssigned F C) (toAssigned F U.cover) U.left U.leftSmooth ∧
      IsFanSubcoverCompatibility R Q (descent F E) (descent F U.cover)
        (toAssigned F E) (toAssigned F U.cover) U.right U.rightSmooth ∧
      ∀ k : Fin ((R.resolution U.cover.total).length),
        ((∀ i : Fin C.size,
          ((descent F U.cover).component (U.partition (.inl i))).tower.toFan.center k =
            FineFan.wholeIdeal
              (((descent F U.cover).component (U.partition (.inl i))).tower.toFan.level
                k.castSucc) ∧
          IsIso (((descent F U.cover).component (U.partition (.inl i))).tower.toFan.arrow
            k).map) ↔
        (∀ i : Fin E.size,
          ((descent F U.cover).component (U.partition (.inr i))).tower.toFan.center k =
            FineFan.wholeIdeal
              (((descent F U.cover).component (U.partition (.inr i))).tower.toFan.level
                k.castSucc) ∧
          IsIso (((descent F U.cover).component (U.partition (.inr i))).tower.toFan.arrow
            k).map))
  arbitraryAffineLift : ∀ M : ResolutionInput.{u},
    (∃ c : Chart M.monoscheme.space, c.openSet = ⊤) →
      Nonempty (SharpResolutionIdentification (R.resolution M) (Q.resolution M.toFan))
  localSmoothModel : ∀ (F G : FineFan.ResolutionInput.{u})
    (g : FineFan.Hom G.fan F.fan), g.IsSmooth →
      ∀ y : G.fan.space, Nonempty (SmoothFanNeighborhoodModel g y)
  smoothUnion : ∀ (F G : FineFan.ResolutionInput.{u})
    (g : FineFan.Hom G.fan F.fan) (hg : g.IsSmooth),
      ∃ (C : AffineLiftCover F) (E : AffineLiftCover G) (U : SmoothCoverUnion g C E)
        (T : SubunionFanTower R C U.total U.target U.targetSmooth)
        (S : SubunionFanTower R E U.total U.source U.sourceSmooth),
        ∃ p : FineFan.PullbackTower T.tower S.tower,
          (p.lift 0).map = eqToHom (congrArg FineFan.Fan.space S.base) ≫ g.map ≫
            eqToHom (congrArg FineFan.Fan.space T.base.symm) ∧
          ∃ (c : FineFan.Contraction T.tower (Q.resolution F).tower)
            (d : FineFan.Contraction S.tower (Q.resolution G).tower),
            (c.iso 0).hom =
              eqToHom (congrArg FineFan.Fan.space
                (T.base.trans (Q.resolution F).base.symm)) ≫
              eqToHom (congrArg (fun j ↦ ((Q.resolution F).tower.level j).space)
                c.first.symm) ∧
            (d.iso 0).hom =
              eqToHom (congrArg FineFan.Fan.space
                (S.base.trans (Q.resolution G).base.symm)) ≫
              eqToHom (congrArg (fun j ↦ ((Q.resolution G).tower.level j).space)
                d.first.symm) ∧
            ∀ k : Fin ((R.resolution U.total).length + 1),
              d.index k = (Q.comparison g hg).contraction.index (c.index k) ∧
              HEq ((d.iso k).inv ≫ (p.lift k).map ≫ (c.iso k).hom)
                ((Q.comparison g hg).levelMap (c.index k))
  fractions : ∀ (F G : FineFan.ResolutionInput.{u})
    (g : FineFan.Hom G.fan F.fan) (y : G.fan.space)
    (M : SmoothFanNeighborhoodModel g y) [DecidableEq M.source.monoid]
    (E : Finset M.target.monoid) (a : M.target.monoid),
    a ∈ E → ∃ f : FineFan.saturatedChart M.target.monoid E a →*
        FineFan.saturatedChart M.source.monoid
          (E.image (smoothFanModelInclusion M.rank M.product))
          (smoothFanModelInclusion M.rank M.product a),
      ∀ q, (f q).val =
        Algebra.GrothendieckGroup.lift
          (Algebra.GrothendieckGroup.of.comp
            (smoothFanModelInclusion M.rank M.product)) q.val
  localDeletion : ∀ (F : FineFan.ResolutionInput.{u}) (C : AffineLiftCover F)
    (k : Fin ((R.resolution C.total).length)),
    ((descent F C).tower.center k =
        FineFan.wholeIdeal ((descent F C).tower.level k.castSucc) ∧
      IsIso ((descent F C).tower.arrow k).map) ↔
    ∀ i : Fin C.size,
      ((descent F C).component i).tower.toFan.center k =
        FineFan.wholeIdeal (((descent F C).component i).tower.toFan.level k.castSucc) ∧
      IsIso (((descent F C).component i).tower.toFan.arrow k).map
  idealComposition : ∀ (F G H : FineFan.Fan.{u})
    (g : FineFan.Hom G F) (h : FineFan.Hom H G) (k : FineFan.Hom H F),
    k.map = h.map ≫ g.map → ∀ I : FineFan.IdealFamily F,
      FineFan.IsNonemptyCoherentIdeal I →
        FineFan.pullbackIdeal k I = FineFan.pullbackIdeal h (FineFan.pullbackIdeal g I)
  deletedTransport : ∀ (n : ℕ) (T : FineFan.Tower.{u} n) (i : Fin n),
    T.center i = FineFan.wholeIdeal (T.level i.castSucc) →
      ∀ e : (T.level i.succ).space ≅ (T.level i.castSucc).space,
        e.hom = (T.arrow i).map →
          ∀ (H : FineFan.Fan.{u}) (f : H.space ⟶ (T.level i.succ).space)
            (I : FineFan.IdealFamily (T.level i.succ)),
            FineFan.IsNonemptyCoherentIdeal I →
              FineFan.pullbackAlong (f ≫ e.hom) (FineFan.pullbackAlong e.inv I) =
                FineFan.pullbackAlong f I

/-- Affine-lift descent is independent of covers and affine lift replacements, and
is compatible with every smooth fan map, identities and composition. The fan rule
in the conclusion contains the contracted recursive pullbacks, their precise
surviving-index equations, and their level-map equations, not just object isomorphisms.

Source: ILO VIII 3.1.13--3.1.16, 3.1.22, 3.1.25--3.1.27, pp.100--102,
and Remark 2.3.5(ii)--(iii), p.92
(blueprint: lem-trf-fan-descent-refinement-pullback).

Proof:
1. Apply R once to the disjoint union of the lifts of two covers. Component
   inclusions are smooth. Use lem-trf-affine-lift-tower-descent to glue its full
   sharpened restrictions, retaining the original indices.
2. A center is whole precisely when it is whole on a cover, and an arrow is an
   isomorphism precisely when its restrictions are. Thus both subcovers delete
   exactly the same original indices. The uniqueness in the descent lemma fixes
   the comparisons with their ordered centers and arrows.
3. For three covers use the single union of all their lifts. The comparisons fix
   original monoid sections and fractions b/a; consequently their composites agree
   on every saturated chart and localization. This proves the refinement cocycle.
4. An arbitrary affine lift over S(B) splits as B times a free unit group, by
   lem-trf-fine-monoid-unit-splitting. The common product of two unit groups maps
   smoothly and surjectively to both lifts. Synchronization and
   lem-trf-sharpening-blowup-chart-comparison identify their full towers over S(B).
5. On the smallest neighborhoods of y and g(y), use
   lem-trf-affine-fan-localization-sections and lem-trf-affine-fan-hom-universal
   to realize g by B to B times N^r. A face in this product inverts exactly t free
   coordinates, giving B' to B' times N^(r-t) times Z^t at every prime.
6. Put the finite source and target affine models in one disjoint union. The two
   maps from a source model pull back its single R tower identically at every
   original index, by lem-trf-smooth-tower-index-synchronization. Sharpening gives
   the pulled-back ideals and the fraction substitutions b/a to g(b)/g(a).
7. These substitutions agree on overlaps. Induct on original indices and glue,
   using lem-trf-affine-lift-tower-descent, to identify the full recursive towers.
8. Whole-ideal isomorphisms stay removable under smooth pullback: in the local
   product charts saturation of P times N^r times Z^s is equivalent to saturation
   of P. Deleting such an isomorphism transports all later ideals unchanged.
9. Generated images satisfy h*(g*I)=(gh)*I: the extra intermediate factor is
   absorbed into the final monoid factor, and the reverse inclusion uses 1.
   Fraction substitutions compose on numerators and denominators, hence on their
   group completions, saturations and overlaps.
10. Induct on the ordered original indices. A previously deleted stage remains
    removable; at all other stages the final tests agree. Thus successive
    contraction and one contraction have the same indices and level maps.
    Identity substitutions give the identity comparisons. Steps 3 and 4 make
    these equations independent of covers and lifts.
11. For the empty fan and empty cover, the descent lemma gives length zero.
    Whole-ideal stages giving a nontrivial initial saturation are retained.
-/
theorem fan_descent_refinement_pullback (R : SmoothFunctorialDesingularization.{u}) :
    ∃ Q : FineFan.SmoothFunctorialDesingularization.{u},
      Nonempty (FanDescentRefinementData R Q) := by
  sorry

end AlgebraicGeometry.Monoscheme
