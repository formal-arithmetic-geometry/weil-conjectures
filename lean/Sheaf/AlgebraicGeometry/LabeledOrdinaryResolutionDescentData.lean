/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryTowerCartesianMap
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Cover.Open
public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Labeled ordinary resolution and affine descent data

Source: ILO, Travaux de Gabber, VIII 2.1.4--2.1.9, 2.3.4--2.3.5(ii), pp.87--88,91--92
(blueprint: def-trf-labeled-ordinary-resolution-descent-data).

The total space of a finite affine cover is its coproduct, with its universal property.
The whole coproduct carries one tower; component towers are never synchronized by choice.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.OrdinaryResolutionDescent

/-- The intrinsic domain admitting a smooth separated finite-type rational ambient scheme.
Source: ILO VIII 2.3.4--2.3.5 (blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
def Embeddable (S : RationalResolutionInput.{u}) : Prop :=
  ∃ (P : Scheme.{u}) (p : P ⟶ Spec (.of (ULift.{u} ℚ))) (j : S.scheme ⟶ P),
    IsClosedImmersion j ∧ Smooth p ∧ IsSeparated p ∧ LocallyOfFiniteType p ∧
      QuasiCompact p ∧ j ≫ p = S.structureMap

/-- A regular ordinary resolution with a strictly increasing list in the fixed label order.
The ideal is coherent as an actual module, not merely as its underlying closed support.
Source: ILO VIII 2.3.1,2.3.4 (blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
structure LabeledTower (L : Type w) [LinearOrder L] (S : Scheme.{u}) where
  tower : OrdinaryBlowupTower S
  labels : Fin tower.length ↪o L
  regular : tower.IsRegularResolution
  coherent : ∀ i : Fin tower.length, RingedSpace.IsCoherent (tower.level i.castSucc).toRingedSpace
    (tower.center i).toModules

/-- A contracted comparison preserving exactly the surviving original labels.
Source: ILO VIII 2.3.4--2.3.5(i)
(blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
structure Comparison {L : Type w} [LinearOrder L] {S T : Scheme.{u}}
    (h : T ⟶ S) (A : LabeledTower L S) (B : LabeledTower L T)
    extends OrdinaryResolutionComparison h A.tower B.tower where
  labels_eq : ∀ k, B.labels k = A.labels (retainedStage k)

/-- An uncontracted cartesian identification retaining every center and every label.
Source: ILO VIII 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
structure CoverIdentification {L : Type w} [LinearOrder L] {S T : Scheme.{u}}
    (h : T ⟶ S) (A : LabeledTower L S) (B : LabeledTower L T)
    extends OrdinaryTowerCartesianMap h A.tower B.tower where
  labels_eq : ∀ k, B.labels k = A.labels (Fin.cast length_eq k)

/-- A finite affine open covering and its disjoint union as a whole rational input.
A chosen coproduct model is allowed only with its universal property. The empty cover
and empty affine opens are allowed. No separatedness of the covered scheme is imposed.
Source: ILO VIII 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
structure AffineCover (S : RationalResolutionInput.{u}) where
  cover : S.scheme.AffineOpenCover.{u}
  finite : Finite cover.I₀
  total : RationalResolutionInput.{u}
  component : ∀ b, Spec (cover.X b) ⟶ total.scheme
  isCoproduct : IsColimit (Cofan.mk total.scheme component)
  map : total.scheme ⟶ S.scheme
  component_map : ∀ b, component b ≫ map = cover.f b
  over : map ≫ S.structureMap = total.structureMap
  embeddable : Embeddable total

/-- The intrinsic algorithm on the embeddable domain, with specified smooth comparisons.
Source: ILO VIII 2.3.4 (blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
structure LocalRule (L : Type w) [LinearOrder L] where
  tower : ∀ (S : RationalResolutionInput.{u}), Embeddable S → LabeledTower L S.scheme
  comparison : ∀ (S T : RationalResolutionInput.{u}) (eS : Embeddable S)
    (eT : Embeddable T) (h : T.scheme ⟶ S.scheme)
    (_over : h ≫ S.structureMap = T.structureMap) [Smooth h],
    Comparison h (tower S eS) (tower T eT)

/-- Equality of a global comparison with the prescribed local comparison on two covers.
Both the count and the ordered survivor embedding are compared, and the square of the
actual level morphisms commutes. This includes every subordinate affine-cover map.
Source: ILO VIII 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
structure Restricts {L : Type w} [LinearOrder L]
    {S T : RationalResolutionInput.{u}} {h : T.scheme ⟶ S.scheme}
    {R : ∀ X : RationalResolutionInput.{u}, LabeledTower L X.scheme}
    {A : LocalRule.{u, w} L} (c : Comparison h (R S) (R T))
    (U : AffineCover S) (V : AffineCover T)
    (a : CoverIdentification U.map (R S) (A.tower U.total U.embeddable))
    (b : CoverIdentification V.map (R T) (A.tower V.total V.embeddable))
    {v : V.total.scheme ⟶ U.total.scheme}
    (q : Comparison v (A.tower U.total U.embeddable) (A.tower V.total V.embeddable)) where
  count_eq : ∀ i, Fin.cast (congrArg Nat.succ b.length_eq)
    (q.count (Fin.cast (congrArg Nat.succ a.length_eq.symm) i)) = c.count i
  retained_eq : ∀ k, Fin.cast a.length_eq.symm
    (c.retainedStage (Fin.cast b.length_eq k)) = q.retainedStage k
  map_eq : ∀ i,
    b.map (q.count (Fin.cast (congrArg Nat.succ a.length_eq.symm) i)) ≫
      eqToHom (congrArg (R T).tower.level (count_eq i)) ≫ c.levelMap i =
    q.levelMap (Fin.cast (congrArg Nat.succ a.length_eq.symm) i) ≫
      a.map (Fin.cast (congrArg Nat.succ a.length_eq.symm) i)

/-- The descent hypothesis: the regular towers have uncontracted identifications on every
finite affine cover. The last two fields state the cover-comparison cocycle as equality
of counts and level maps. The center equality is already in `CoverIdentification`.
Source: ILO VIII 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
structure Datum (L : Type w) [LinearOrder L] where
  localRule : LocalRule.{u, w} L
  tower : ∀ S : RationalResolutionInput.{u}, LabeledTower L S.scheme
  cover : ∀ (S : RationalResolutionInput.{u}) (U : AffineCover S),
    CoverIdentification U.map (tower S) (localRule.tower U.total U.embeddable)
  cocycle_count : ∀ (S : RationalResolutionInput.{u}) (U V : AffineCover S)
    (v : V.total.scheme ⟶ U.total.scheme) (_hv : v ≫ U.map = V.map)
    (overV : v ≫ U.total.structureMap = V.total.structureMap) [Smooth v] i,
    Fin.cast (congrArg Nat.succ (cover S V).length_eq)
      ((localRule.comparison U.total V.total U.embeddable V.embeddable v overV).count i) =
      Fin.cast (congrArg Nat.succ (cover S U).length_eq) i
  cocycle_map : ∀ (S : RationalResolutionInput.{u}) (U V : AffineCover S)
    (v : V.total.scheme ⟶ U.total.scheme) (hv : v ≫ U.map = V.map)
    (overV : v ≫ U.total.structureMap = V.total.structureMap) [Smooth v] i,
    (cover S V).map
      ((localRule.comparison U.total V.total U.embeddable V.embeddable v overV).count i) ≫
        eqToHom (congrArg (tower S).tower.level (cocycle_count S U V v hv overV i)) =
    (localRule.comparison U.total V.total U.embeddable V.embeddable v overV).levelMap i ≫
      (cover S U).map i

/-- The canonical blowup normalization of each retained step. After any identification
of the equal extended center ideals over the lower level, the upper level map is exactly
the published flat blowup base-change map. That map is constructed from coefficientwise
Rees pullback, hence on affine charts is the tensor base-change identification, including
its fraction formula. The hypotheses below test all such identifications; they do not
supply extra data to the descent theorem.
Source: ILO VIII 2.1.9; Stacks 0805
(blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
def CanonicalSteps {L : Type w} [LinearOrder L] {S T : Scheme.{u}}
    {h : T ⟶ S} {A : LabeledTower L S} {B : LabeledTower L T}
    (c : Comparison h A B) : Prop :=
  ∀ (k : Fin B.tower.length)
    (f : B.tower.level k.castSucc ⟶ A.tower.level (c.retainedStage k).castSucc)
    (_hf : f = eqToHom (congrArg B.tower.level (c.count_before k).symm) ≫
      c.levelMap (c.retainedStage k).castSucc) [Flat f]
    (e : (B.tower.center k).blowup ≅ ((A.tower.center (c.retainedStage k)).comap f).blowup),
    e.hom ≫ ((A.tower.center (c.retainedStage k)).comap f).blowupMap =
      (B.tower.center k).blowupMap →
    eqToHom (congrArg B.tower.level (c.count_after k).symm) ≫
        c.levelMap (c.retainedStage k).succ =
      (B.tower.blowupIso k).hom ≫ e.hom ≫
        ((A.tower.center (c.retainedStage k)).blowupFlatBaseChangeIso f).hom ≫
          pullback.fst _ _ ≫ (A.tower.blowupIso (c.retainedStage k)).inv

/-- Transport a rule's existing comparison along equality of its assigned towers.
Source: ILO VIII 2.3.4 (blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
def transportComparison {L : Type w} [LinearOrder L]
    (F : SmoothFunctorialOrdinaryResolution.{u})
    (R : ∀ S : RationalResolutionInput.{u}, LabeledTower L S.scheme)
    (e : ∀ S, F.tower S = (R S).tower)
    (S T : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (over : h ≫ S.structureMap = T.structureMap) [Smooth h] :
    OrdinaryResolutionComparison h (R S).tower (R T).tower :=
  (e S) ▸ (e T) ▸ F.comparison S T h over

/-- A global smooth rule on the given towers, with the given labels. Identity,
composition of counts and level maps, cartesian squares, extended center ideals and
surjective nondeletion use the existing ordinary-resolution-rule interface.
Source: ILO VIII 2.3.4--2.3.5
(blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
structure GlobalRule {L : Type w} [LinearOrder L] (D : Datum.{u, w} L) where
  rule : SmoothFunctorialOrdinaryResolution.{u}
  tower_eq : ∀ S, rule.tower S = (D.tower S).tower
  labels_eq : ∀ (S T : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (over : h ≫ S.structureMap = T.structureMap) [Smooth h] k,
    (D.tower T).labels k = (D.tower S).labels
      ((transportComparison rule D.tower tower_eq S T h over).retainedStage k)

/-- The labeled comparison underlying a global rule, on the original specified towers.
Source: ILO VIII 2.3.4 (blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
def GlobalRule.comparison {L : Type w} [LinearOrder L] {D : Datum.{u, w} L}
    (F : GlobalRule D) (S T : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (over : h ≫ S.structureMap = T.structureMap) [Smooth h] :
    Comparison h (D.tower S) (D.tower T) where
  toOrdinaryResolutionComparison := transportComparison F.rule D.tower F.tower_eq S T h over
  labels_eq := F.labels_eq S T h over

/-- All conclusions of affine-cover descent, including agreement with every specified
local comparison, unit deletion on every lifted affine, ordered deletion composition,
the canonical blowup chart maps, and triviality on the empty input. Cover independence
is literal: one comparison must restrict correctly for every pair of covers at once.
Source: ILO VIII 2.1.9,2.3.4--2.3.5
(blueprint: def-trf-labeled-ordinary-resolution-descent-data). -/
structure DescendedRule {L : Type w} [LinearOrder L] (D : Datum.{u, w} L)
    extends GlobalRule D where
  restricts : ∀ (S T : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (over : h ≫ S.structureMap = T.structureMap) [Smooth h]
    (U : AffineCover S) (V : AffineCover T)
    (v : V.total.scheme ⟶ U.total.scheme) (_square : v ≫ U.map = V.map ≫ h)
    (overV : v ≫ U.total.structureMap = V.total.structureMap) [Smooth v],
    Nonempty (Restricts (toGlobalRule.comparison S T h over) U V (D.cover S U) (D.cover T V)
      (D.localRule.comparison U.total V.total U.embeddable V.embeddable v overV))
  deleted_locally : ∀ (S T : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (over : h ≫ S.structureMap = T.structureMap) [Smooth h]
    (V : AffineCover T) (i : Fin (D.tower S).tower.length),
    i ∉ Set.range (toGlobalRule.comparison S T h over).retainedStage ↔
      ∀ b, ((D.tower S).tower.center i).comap
        (pullback.fst
          ((D.tower T).tower.toBase ((toGlobalRule.comparison S T h over).count i.castSucc))
          (V.cover.f b) ≫ (toGlobalRule.comparison S T h over).levelMap i.castSucc) = ⊤
  identity_retained : ∀ (S : RationalResolutionInput.{u}) k,
    (toGlobalRule.comparison S S (𝟙 S.scheme) (by simp)).retainedStage k = k
  composition_retained : ∀ (S T Z : RationalResolutionInput.{u})
    (h : T.scheme ⟶ S.scheme) (g : Z.scheme ⟶ T.scheme)
    (overH : h ≫ S.structureMap = T.structureMap)
    (overG : g ≫ T.structureMap = Z.structureMap) [Smooth h] [Smooth g] k,
    (toGlobalRule.comparison S Z (g ≫ h)
      (by rw [Category.assoc, overH, overG])).retainedStage k =
    (toGlobalRule.comparison S T h overH).retainedStage
      ((toGlobalRule.comparison T Z g overG).retainedStage k)
  canonical_steps : ∀ (S T : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (over : h ≫ S.structureMap = T.structureMap) [Smooth h],
    CanonicalSteps (toGlobalRule.comparison S T h over)
  empty_trivial : ∀ (S : RationalResolutionInput.{u}) (eS : Embeddable S),
    IsEmpty S.scheme → (D.localRule.tower S eS).tower.length = 0 →
      (D.tower S).tower.length = 0

end AlgebraicGeometry.OrdinaryResolutionDescent
