/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryTowerCartesianMap
public import Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Labeled ordinary towers and Zariski resolution data

Source: ILO, Travaux de Gabber, VIII 2.1.4--2.1.9, 2.3.1, 2.3.4,
Remark 2.3.5(ii), printed pp.87--88,91--92
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data).

These are data, not an assertion of existence of a resolution or of descent.
The ordinary towers, contracted comparisons and uncontracted cartesian maps are reused.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Membership in the embedded input class is existential, so an input carries no chosen
embedding. Finite disjoint unions are allowed by the existing embedded-pair definition.
Source: ILO VIII 2.3.5(ii), 2.3.11--2.3.13
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
def RationalResolutionInput.IsEmbeddable (S : RationalResolutionInput.{u}) : Prop :=
  ∃ (P : EmbeddedResolutionPair.{u}) (e : S.scheme ≅ P.X),
    e.hom ≫ P.inclusion ≫ P.base = S.structureMap

/-- Distinct increasing labels on an existing finite ordinary tower. No center is removed
by this definition, so it also accommodates padded towers with unit-ideal stages.
Source: ILO VIII 2.1.4, 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
structure LabeledOrdinaryTower (L : Type w) [LinearOrder L] (X : Scheme.{u}) where
  tower : OrdinaryBlowupTower X
  label : Fin tower.length ↪o L

/-- Label-preserving contraction: the inherited comparison deletes exactly unit ideals
and is cartesian at every level, with equality of the full extended ideals.
Source: ILO VIII 2.1.9, 2.3.4--2.3.5
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
structure LabeledOrdinaryComparison {L : Type w} [LinearOrder L]
    {X Y : Scheme.{u}} (h : Y ⟶ X)
    (A : LabeledOrdinaryTower L X) (B : LabeledOrdinaryTower L Y)
    extends OrdinaryResolutionComparison h A.tower B.tower where
  labels : ∀ k, B.label k = A.label (retainedStage k)

/-- An uncontracted comparison also preserves every label. Over the identity of the
base its cartesian level maps are isomorphisms, so this is a tower isomorphism with centers.
Source: ILO VIII 2.1.7--2.1.9, 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
structure LabeledOrdinaryCartesianMap {L : Type w} [LinearOrder L]
    {X Y : Scheme.{u}} (h : Y ⟶ X)
    (A : LabeledOrdinaryTower L X) (B : LabeledOrdinaryTower L Y)
    extends OrdinaryTowerCartesianMap h A.tower B.tower where
  labels : ∀ k, B.label k = A.label (Fin.cast length_eq k)

/-- Equality with the composite on every level. Casts only identify finite index sets;
all three maps preserve the full centers and labels by their structure fields.
Source: ILO VIII Remark 2.3.5(ii), canonical comparison cocycle
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
def LabeledOrdinaryCartesianMap.IsComposite {L : Type w} [LinearOrder L]
    {X : Scheme.{u}} {B C D : LabeledOrdinaryTower L X}
    (bc : LabeledOrdinaryCartesianMap (𝟙 X) B C)
    (cd : LabeledOrdinaryCartesianMap (𝟙 X) C D)
    (bd : LabeledOrdinaryCartesianMap (𝟙 X) B D) : Prop :=
  ∀ i : Fin (D.tower.length + 1),
    cd.map i ≫ bc.map (Fin.cast (congrArg Nat.succ cd.length_eq) i) = bd.map i

/-- A finite affine open covering with its actual disjoint union, expressed by the
coproduct universal property. All structural morphisms are over the rational field.
There is no affine-intersection or separatedness condition, and the empty family is allowed.
Source: ILO VIII Remark 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
structure ResolutionAffineCover (S T : RationalResolutionInput.{u})
    (q : T.scheme ⟶ S.scheme) where
  size : ℕ
  chart : Fin size → S.scheme.affineOpens
  inclusion : ∀ a, (chart a).1.toScheme ⟶ T.scheme
  coproduct : IsColimit (Cofan.mk T.scheme inclusion)
  factor : ∀ a, inclusion a ≫ q = (chart a).1.ι
  covers : ∀ x : S.scheme, ∃ a, x ∈ (chart a).1
  over : q ≫ S.structureMap = T.structureMap

/-- The good towers have the prescribed regular nonempty nowhere dense centers and regular
last level. Coherence is stated using the exact sheaf predicate, and finite type is recorded
on every level with its actual composite structure morphism.
Source: ILO VIII 2.3.1, 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
def LabeledOrdinaryTower.IsResolution {L : Type w} [LinearOrder L]
    {S : RationalResolutionInput.{u}} (A : LabeledOrdinaryTower L S.scheme) : Prop :=
  A.tower.IsRegularResolution ∧
    (∀ i : Fin A.tower.length,
      RingedSpace.IsCoherent (A.tower.level i.castSucc).toRingedSpace
        (A.tower.center i).toModules) ∧
    (∀ i : Fin (A.tower.length + 1),
      LocallyOfFiniteType (A.tower.toBase i ≫ S.structureMap) ∧
      QuasiCompact (A.tower.toBase i ≫ S.structureMap))

/-- An ordinary resolution assignment on the embeddable inputs, with canonical open
contraction comparisons. No assertion of existence, no smooth functoriality assumption,
and no stop-at-regular hypothesis is included.
Source: ILO VIII 2.3.4 and Remark 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
structure OrdinaryZariskiResolutionRule (L : Type w) [LinearOrder L] where
  tower : ∀ (S : RationalResolutionInput.{u}), S.IsEmbeddable → LabeledOrdinaryTower L S.scheme
  resolves : ∀ S hS, (tower S hS).tower.IsRegularResolution
  coherent : ∀ S hS (i : Fin (tower S hS).tower.length),
    RingedSpace.IsCoherent ((tower S hS).tower.level i.castSucc).toRingedSpace
      ((tower S hS).tower.center i).toModules
  empty : ∀ S hS, IsEmpty S.scheme → (tower S hS).tower.length = 0
  comparison : ∀ (S T : RationalResolutionInput.{u}) (hS : S.IsEmbeddable)
    (hT : T.IsEmbeddable) (j : T.scheme ⟶ S.scheme),
    IsOpenImmersion j → j ≫ S.structureMap = T.structureMap →
      LabeledOrdinaryComparison j (tower S hS) (tower T hT)

/-- Ideal descent includes uniqueness of the ideal on each global level, as well as
its restriction equality already present in the cartesian comparison's `centers` field.
Source: ILO VIII Remark 2.3.5(ii), ideal descent
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
def LabeledOrdinaryCartesianMap.DescendsIdeals {L : Type w} [LinearOrder L]
    {X Y : Scheme.{u}} {h : Y ⟶ X}
    {A : LabeledOrdinaryTower L X} {B : LabeledOrdinaryTower L Y}
    (c : LabeledOrdinaryCartesianMap h A B) : Prop :=
  ∀ (i : Fin B.tower.length)
    (J : (A.tower.level (Fin.cast c.length_eq i).castSucc).IdealSheafData),
    J.comap (c.map i.castSucc) = B.tower.center i →
      J = A.tower.center (Fin.cast c.length_eq i)

/-- A global tower realizes a chosen affine-cover construction if its full cartesian
pullback is the assigned disjoint-union tower. No contraction is permitted here.
Source: ILO VIII Remark 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
def OrdinaryZariskiResolutionRule.IsAffineDescent {L : Type w} [LinearOrder L]
    (A : OrdinaryZariskiResolutionRule.{u, w} L) (S : RationalResolutionInput.{u})
    (B : LabeledOrdinaryTower L S.scheme) : Prop :=
  ∃ (T : RationalResolutionInput.{u}) (q : T.scheme ⟶ S.scheme),
    Nonempty (ResolutionAffineCover S T q) ∧
      ∃ hT : T.IsEmbeddable, Nonempty (LabeledOrdinaryCartesianMap q B (A.tower T hT))

/-- Synchronized affine descent is tested on every finite affine cover, including the
empty one. The actual total space is a coproduct, not an arbitrary surjective map.
Source: ILO VIII Remark 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
def OrdinaryZariskiResolutionRule.IsSynchronizedDescent {L : Type w} [LinearOrder L]
    (A : OrdinaryZariskiResolutionRule.{u, w} L) (S : RationalResolutionInput.{u})
    (B : LabeledOrdinaryTower L S.scheme) : Prop :=
  ∀ (T : RationalResolutionInput.{u}) (q : T.scheme ⟶ S.scheme),
    ResolutionAffineCover S T q → ∃ hT : T.IsEmbeddable,
      ∃! c : LabeledOrdinaryCartesianMap q B (A.tower T hT), c.DescendsIdeals

/-- On an affine overlap all three full restrictions are one padded tower. Taking two
of the three maps equal gives the double-overlap assertion. The contracted comparison to
`A(W)` retains its labels and deletes exactly unit ideals; hence the common full tower
is obtained by restoring precisely the missing unit-ideal identity stages. Its single
common realization gives the triple-overlap cocycle, not just pairwise terminal isomorphisms.
Source: ILO VIII 2.1.9 and Remark 2.3.5(ii)
(blueprint: def-trf-labeled-ordinary-zariski-resolution-data). -/
def OrdinaryZariskiResolutionRule.HasPaddedOverlaps {L : Type w} [LinearOrder L]
    (A : OrdinaryZariskiResolutionRule.{u, w} L) : Prop :=
  ∀ (S T : RationalResolutionInput.{u}) (q : T.scheme ⟶ S.scheme)
    (_cover : ResolutionAffineCover S T q) (hT : T.IsEmbeddable)
    (W : RationalResolutionInput.{u}) (hW : W.IsEmbeddable),
    IsAffine W.scheme → ∀ (v : W.scheme ⟶ S.scheme)
      (j : Fin 3 → (W.scheme ⟶ T.scheme)),
      IsOpenImmersion v → v ≫ S.structureMap = W.structureMap →
      (∀ a, IsOpenImmersion (j a)) → (∀ a, j a ≫ q = v) →
      ∃ P : LabeledOrdinaryTower L W.scheme,
        (∀ a, Nonempty (LabeledOrdinaryCartesianMap (j a) (A.tower T hT) P)) ∧
          Nonempty (LabeledOrdinaryComparison (𝟙 W.scheme) P (A.tower W hW))

end AlgebraicGeometry
