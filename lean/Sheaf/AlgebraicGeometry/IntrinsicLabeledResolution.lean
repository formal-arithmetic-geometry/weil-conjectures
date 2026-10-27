/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-!
# Intrinsic labeled ordinary resolution on embeddable rational schemes

Source: ILO VIII 2.1.4--2.1.9, 2.3.4--2.3.5, 2.3.11--2.3.13, pp.87--88,91--94
(blueprint: def-trf-intrinsic-labeled-resolution).

The cut diagram is linked to an actual finite ordinary tower, including its ideals.
It records repeated levels at deleted labels without making choices of pullback schemes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A permitted embedding of a rational input, allowing an isomorphic model of its scheme.
The rational structure is respected. Source: ILO VIII 2.3.11--2.3.13
(blueprint: def-trf-intrinsic-labeled-resolution). -/
structure RationalResolutionEmbedding (S : RationalResolutionInput.{u}) where
  pair : EmbeddedResolutionPair.{u}
  iso : S.scheme ≅ pair.X
  over : iso.hom ≫ pair.inclusion ≫ pair.base = S.structureMap

/-- The class of embeddable reduced finite-type rational inputs; membership is a property,
not a chosen embedding. Source: ILO VIII 2.3.11--2.3.13
(blueprint: def-trf-intrinsic-labeled-resolution). -/
def EmbeddableResolutionInput :=
  {S : RationalResolutionInput.{u} // Nonempty (RationalResolutionEmbedding S)}

/-- A finite ordinary regular resolution with strictly increasing labels, also indexed by
all lower cuts. `index` counts the labels in a cut; `stage` identifies its diagram with
exactly that level of the ordinary tower, naturally and preserving center ideals. Thus
identity blowups at nonempty centers remain recorded. Source: ILO VIII 2.1.4--2.1.9,
2.3.1, 2.3.4--2.3.5 (blueprint: def-trf-intrinsic-labeled-resolution). -/
structure IntrinsicLabeledOrdinaryTower (L : Type w) [LinearOrder L] (X : Scheme.{u}) where
  ordinary : OrdinaryBlowupTower X
  resolves : ordinary.IsRegularResolution
  label : Fin ordinary.length ↪o L
  diagram : (LowerSet L)ᵒᵖ ⥤ Scheme.{u}
  index : LowerSet L →o Fin (ordinary.length + 1)
  index_labels : ∀ s (i : Fin ordinary.length), i.val < (index s).val ↔ label i ∈ s
  index_bot : index ⊥ = 0
  index_top : index ⊤ = Fin.last ordinary.length
  index_before : ∀ i, index (LowerSet.Iio (label i)) = i.castSucc
  stage : ∀ s, diagram.obj (op s) ≅ ordinary.level (index s)
  stage_naturality : ∀ (s t : LowerSet L) (h : s ≤ t),
    diagram.map (homOfLE h).op ≫ (stage s).hom =
      (stage t).hom ≫ ordinary.transition (index s) (index t) (index.monotone h)
  center : ∀ l : L, (diagram.obj (op (LowerSet.Iio l))).IdealSheafData
  center_ordinary : ∀ i, center (label i) = (ordinary.center i).comap
    ((stage (LowerSet.Iio (label i))).hom ≫
      eqToHom (congrArg ordinary.level (index_before i)))
  center_absent : ∀ l, l ∉ Set.range label → center l = ⊤
  coherent : ∀ l, (center l).toModules.IsFiniteTypeWithFiniteTypeKernels
  regular_input : IsRegularScheme X → ordinary.length = 0
  empty_input : IsEmpty X → ordinary.length = 0

/-- The cut-level structure map to the initial input. Source: ILO VIII 2.1.4
(blueprint: def-trf-intrinsic-labeled-resolution). -/
def IntrinsicLabeledOrdinaryTower.toBase {L : Type w} [LinearOrder L] {X : Scheme.{u}}
    (A : IntrinsicLabeledOrdinaryTower L X) (s : LowerSet L) :
    A.diagram.obj (op s) ⟶ X :=
  (A.stage s).hom ≫ A.ordinary.toBase (A.index s)

/-- A contracted cartesian pullback at every cut, keeping precisely nonunit extended
ideals and their original labels. Naturality includes all tower transitions.
Source: ILO VIII 2.1.9, 2.3.4--2.3.5
(blueprint: def-trf-intrinsic-labeled-resolution). -/
structure IntrinsicLabeledResolutionPullback {L : Type w} [LinearOrder L]
    {X Y : Scheme.{u}} (h : Y ⟶ X)
    (A : IntrinsicLabeledOrdinaryTower L X) (B : IntrinsicLabeledOrdinaryTower L Y) where
  map : B.diagram ⟶ A.diagram
  cartesian : ∀ s, IsPullback (map.app (op s)) (B.toBase s) (A.toBase s) h
  centers : ∀ l, B.center l = (A.center l).comap (map.app (op (LowerSet.Iio l)))
  retained : ∀ l, l ∈ Set.range B.label ↔
    l ∈ Set.range A.label ∧ (A.center l).comap (map.app (op (LowerSet.Iio l))) ≠ ⊤

/-- An identification with the supplied embedded strict-transform diagram, over the
input and preserving the ordered labels and actual intrinsic center ideals.
Source: ILO VIII 2.1.3(ii), 2.3.11--2.3.13
(blueprint: def-trf-intrinsic-labeled-resolution). -/
structure IntrinsicEmbeddedResolutionIdentification {L : Type w} [LinearOrder L]
    {S : RationalResolutionInput.{u}} (A : IntrinsicLabeledOrdinaryTower L S.scheme)
    (p : RationalResolutionEmbedding S) (T : LabeledEmbeddedResolutionTower L p.pair) where
  iso : A.diagram ≅ T.intrinsic
  initial : (iso.app (op ⊥)).hom ≫ T.initialIntrinsic.hom = A.toBase ⊥ ≫ p.iso.hom
  labels : Set.range A.label = (T.labels : Set L)
  centers : ∀ l, A.center l =
    (T.centerToIntrinsic l).ker.comap (iso.app (op (LowerSet.Iio l))).hom

/-- An intrinsic assignment on precisely the embeddable inputs with canonical smooth
comparisons. The comparison is unique with its cartesian and ideal conditions; in
particular choices of charts or lifts cannot change it. `ambient` says exactly that it
recovers the supplied embedded comparison for a cartesian smooth ambient square.
`cocycle` is change of embedding, with no compatibility assumed of the supplied two
kinds of comparison. Source: ILO VIII 2.1.9, 2.3.11--2.3.13
(blueprint: def-trf-intrinsic-labeled-resolution). -/
structure IntrinsicResolutionOfEmbedded (L : Type w) [LinearOrder L]
    (E : SynchronizedEmbeddedResolution.{u, w} L) where
  tower : ∀ S : EmbeddableResolutionInput.{u}, IntrinsicLabeledOrdinaryTower L S.val.scheme
  embedding : ∀ S (p : RationalResolutionEmbedding S.val),
    IntrinsicEmbeddedResolutionIdentification (tower S) p (E.tower p.pair)
  cocycle : ∀ S (p q : RationalResolutionEmbedding S.val),
    (embedding S p).iso ≪≫ (E.intrinsic (p.iso.symm ≪≫ q.iso)).iso = (embedding S q).iso
  comparison : ∀ (S T : EmbeddableResolutionInput.{u}) (h : T.val.scheme ⟶ S.val.scheme)
    (_over : h ≫ S.val.structureMap = T.val.structureMap) [Smooth h],
    IntrinsicLabeledResolutionPullback h (tower S) (tower T)
  unique : ∀ (S T : EmbeddableResolutionInput.{u}) (h : T.val.scheme ⟶ S.val.scheme)
    (over : h ≫ S.val.structureMap = T.val.structureMap) [Smooth h]
    (c : IntrinsicLabeledResolutionPullback h (tower S) (tower T)),
    c = comparison S T h over
  ambient : ∀ (S T : EmbeddableResolutionInput.{u})
    (p : RationalResolutionEmbedding S.val) (q : RationalResolutionEmbedding T.val)
    (h : T.val.scheme ⟶ S.val.scheme) (over : h ≫ S.val.structureMap = T.val.structureMap)
    [Smooth h] (f : EmbeddedResolutionSmoothMap q.pair p.pair),
    q.iso.hom ≫ f.intrinsic = h ≫ p.iso.hom →
      (comparison S T h over).map ≫ (embedding S p).iso.hom =
        (embedding T q).iso.hom ≫ (E.pullback f).intrinsic

end AlgebraicGeometry
