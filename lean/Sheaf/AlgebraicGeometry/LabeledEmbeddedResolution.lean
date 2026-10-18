/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Order.UpperLower.Principal
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre
public import Sheaf.AlgebraicGeometry.IsRegularScheme

/-!
# Labeled embedded resolution data

Source: ILO, Expose VIII, 2.3.1, 2.3.4, 2.3.11--2.3.13; Bierstone--Milman--Temkin,
Q-universal desingularization, Theorem 6.1 and Addendum, section 6.3
(blueprint: def-trf-labeled-embedded-resolution).

Cuts in the common ordered label set index a finite tower with identity stages inserted.
Only finitely many labels are active. Maps across intervals without active labels are
isomorphisms; deleting those stages recovers the ordinary finite tower. Ideal centers,
not just their supports, are retained. All the structures below contain actual data.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A reduced closed subscheme of a smooth separated finite-type rational scheme.
Finite disjoint unions are included: no connectedness or equidimensionality is imposed.
The lift only places the rational base in the scheme universe.
Source: ILO VIII 2.3.11--2.3.13 (blueprint: def-trf-labeled-embedded-resolution). -/
structure EmbeddedResolutionPair where
  X : Scheme.{u}
  P : Scheme.{u}
  base : P ⟶ Spec (.of (ULift.{u} ℚ))
  inclusion : X ⟶ P
  closed : IsClosedImmersion inclusion
  reduced : IsReduced X
  smooth : Smooth base
  separated : IsSeparated base
  finiteType : LocallyOfFiniteType base
  quasiCompact : QuasiCompact base

/-- A smooth ambient map together with its cartesian map on the embedded subschemes.
There is no relative-dimension restriction.
Source: ILO VIII 2.3.4; BMT 6.3 (blueprint: def-trf-labeled-embedded-resolution). -/
structure EmbeddedResolutionSmoothMap (A B : EmbeddedResolutionPair.{u}) where
  ambient : A.P ⟶ B.P
  intrinsic : A.X ⟶ B.X
  smooth : Smooth ambient
  cartesian : IsPullback intrinsic A.inclusion B.inclusion ambient

/-- A finite labeled ordinary embedded blowup tower, extended to all lower cuts by
identity stages. At label `l`, `Iio l` is the state before the center and `Iic l` is
its state after blowing up. Finiteness and `constantAmbient`/`constantIntrinsic`
exclude changes between these finitely many stages. Centers at absent labels are
unit ideals. Regularity forces all remaining stages to be absent, so exceptional
cleanup after resolution is excluded.
Source: ILO VIII 2.3.1, 2.3.4, 2.3.11; BMT 6.1 Addendum
(blueprint: def-trf-labeled-embedded-resolution). -/
structure LabeledEmbeddedResolutionTower (L : Type w) [LinearOrder L]
    (A : EmbeddedResolutionPair.{u}) where
  labels : Finset L
  ambient : (LowerSet L)ᵒᵖ ⥤ Scheme.{u}
  intrinsic : (LowerSet L)ᵒᵖ ⥤ Scheme.{u}
  inclusion : intrinsic ⟶ ambient
  closed : ∀ s, IsClosedImmersion (inclusion.app (op s))
  initialAmbient : ambient.obj (op ⊥) ≅ A.P
  initialIntrinsic : intrinsic.obj (op ⊥) ≅ A.X
  initialInclusion : inclusion.app (op ⊥) ≫ initialAmbient.hom =
    initialIntrinsic.hom ≫ A.inclusion
  constantAmbient : ∀ (s t : LowerSet L) (h : s ≤ t),
    (∀ l ∈ labels, l ∈ s ↔ l ∈ t) → IsIso (ambient.map (homOfLE h).op)
  constantIntrinsic : ∀ (s t : LowerSet L) (h : s ≤ t),
    (∀ l ∈ labels, l ∈ s ↔ l ∈ t) → IsIso (intrinsic.map (homOfLE h).op)
  center : ∀ l : L, (ambient.obj (op (LowerSet.Iio l))).IdealSheafData
  centerToIntrinsic : ∀ l : L,
    (center l).subscheme ⟶ intrinsic.obj (op (LowerSet.Iio l))
  centerClosed : ∀ l, IsClosedImmersion (centerToIntrinsic l)
  centerInclusion : ∀ l, centerToIntrinsic l ≫ inclusion.app (op (LowerSet.Iio l)) =
    (center l).subschemeι
  absentCenter : ∀ l, l ∉ labels → center l = ⊤
  nonemptyCenter : ∀ l ∈ labels, Nonempty (center l).subscheme
  regularCenter : ∀ l ∈ labels, IsRegularScheme (center l).subscheme
  nowhereDense : ∀ l ∈ labels, interior (Set.range (centerToIntrinsic l)) = ∅
  coherentAmbient : ∀ l, (center l).toModules.IsFiniteTypeWithFiniteTypeKernels
  coherentIntrinsic : ∀ l, (centerToIntrinsic l).ker.toModules.IsFiniteTypeWithFiniteTypeKernels
  ambientBlowup : ∀ l ∈ labels,
    ambient.obj (op (LowerSet.Iic l)) ≅ (center l).blowup
  ambientBlowupMap : ∀ (l : L) (hl : l ∈ labels),
    (ambientBlowup l hl).hom ≫ (center l).blowupMap =
      ambient.map (homOfLE (Set.Iio_subset_Iic_self)).op
  strictTransform : ∀ l ∈ labels,
    intrinsic.obj (op (LowerSet.Iic l)) ≅
      (center l).strictTransform (inclusion.app (op (LowerSet.Iio l)))
  strictTransformMap : ∀ (l : L) (hl : l ∈ labels),
    (strictTransform l hl).hom ≫ AlgebraicGeometry.strictTransformMap
      (inclusion.app (op (LowerSet.Iio l))) (center l).blowupMap (center l).support.compl =
      inclusion.app (op (LowerSet.Iic l)) ≫ (ambientBlowup l hl).hom
  strictTransformToSource : ∀ (l : L) (hl : l ∈ labels),
    (strictTransform l hl).hom ≫ AlgebraicGeometry.strictTransformToSource
      (inclusion.app (op (LowerSet.Iio l))) (center l).blowupMap (center l).support.compl =
      intrinsic.map (homOfLE (Set.Iio_subset_Iic_self)).op
  finalRegular : IsRegularScheme (intrinsic.obj (op ⊤))
  stopAtRegular : ∀ s : LowerSet L, IsRegularScheme (intrinsic.obj (op s)) →
    ∀ l ∈ labels, l ∈ s
  regularInput : IsRegularScheme A.X → labels = ∅
  emptyInput : IsEmpty A.X → labels = ∅

/-- Cartesian labeled comparisons of towers under a smooth ambient pullback. The
center ideal is pulled back at each label, including labels whose centers become
empty. Together with `absentCenter` and `nonemptyCenter`, `retainedLabels` says
precisely which stages are deleted.
Source: ILO VIII 2.3.4, 2.3.13; BMT 6.3
(blueprint: def-trf-labeled-embedded-resolution). -/
structure LabeledEmbeddedResolutionPullback {L : Type w} [LinearOrder L]
    {A B : EmbeddedResolutionPair.{u}} (f : EmbeddedResolutionSmoothMap A B)
    (T : LabeledEmbeddedResolutionTower L A) (U : LabeledEmbeddedResolutionTower L B) where
  ambient : T.ambient ⟶ U.ambient
  intrinsic : T.intrinsic ⟶ U.intrinsic
  inclusion : T.inclusion ≫ ambient = intrinsic ≫ U.inclusion
  initialAmbient : ambient.app (op ⊥) ≫ U.initialAmbient.hom =
    T.initialAmbient.hom ≫ f.ambient
  initialIntrinsic : intrinsic.app (op ⊥) ≫ U.initialIntrinsic.hom =
    T.initialIntrinsic.hom ≫ f.intrinsic
  cartesianAmbient : ∀ s : LowerSet L,
    IsPullback (ambient.app (op s))
      (T.ambient.map (homOfLE (bot_le : (⊥ : LowerSet L) ≤ s)).op ≫ T.initialAmbient.hom)
      (U.ambient.map (homOfLE (bot_le : (⊥ : LowerSet L) ≤ s)).op ≫ U.initialAmbient.hom)
      f.ambient
  cartesianIntrinsic : ∀ s : LowerSet L,
    IsPullback (intrinsic.app (op s))
      (T.intrinsic.map (homOfLE (bot_le : (⊥ : LowerSet L) ≤ s)).op ≫
        T.initialIntrinsic.hom)
      (U.intrinsic.map (homOfLE (bot_le : (⊥ : LowerSet L) ≤ s)).op ≫
        U.initialIntrinsic.hom) f.intrinsic
  centers : ∀ l : L, T.center l = (U.center l).comap (ambient.app (op (LowerSet.Iio l)))
  retainedLabels : ∀ l : L, l ∈ T.labels ↔
    l ∈ U.labels ∧ Nonempty ((U.center l).comap (ambient.app (op (LowerSet.Iio l)))).subscheme

/-- An intrinsic comparison induced by an isomorphism of the initial reduced schemes.
It compares strict transforms and their ideal centers, without identifying ambient
schemes, and retains exactly the common labels.
Source: BMT 6.1 Addendum (3), 6.3 (blueprint: def-trf-labeled-embedded-resolution). -/
structure LabeledEmbeddedResolutionIntrinsicComparison {L : Type w} [LinearOrder L]
    {A B : EmbeddedResolutionPair.{u}} (e : A.X ≅ B.X)
    (T : LabeledEmbeddedResolutionTower L A) (U : LabeledEmbeddedResolutionTower L B) where
  iso : T.intrinsic ≅ U.intrinsic
  initial : (iso.app (op ⊥)).hom ≫ U.initialIntrinsic.hom = T.initialIntrinsic.hom ≫ e.hom
  labels : T.labels = U.labels
  centers : ∀ l : L, (T.centerToIntrinsic l).ker =
    (U.centerToIntrinsic l).ker.comap (iso.app (op (LowerSet.Iio l))).hom

/-- A synchronized embedded resolution algorithm is an assignment of these finite towers
with chosen cartesian smooth comparisons and intrinsic isomorphism comparisons satisfying
identity and composition laws. The label order is shared by every input, including finite
disjoint unions. The equations assert coherence of the actual comparison maps.
Source: ILO VIII 2.3.11--2.3.13; BMT Theorem 6.1, Addendum, section 6.3
(blueprint: def-trf-labeled-embedded-resolution). -/
structure SynchronizedEmbeddedResolution (L : Type w) [LinearOrder L] where
  tower : ∀ A : EmbeddedResolutionPair.{u}, LabeledEmbeddedResolutionTower L A
  pullback : ∀ {A B : EmbeddedResolutionPair.{u}} (f : EmbeddedResolutionSmoothMap A B),
    LabeledEmbeddedResolutionPullback f (tower A) (tower B)
  pullbackId : ∀ (A : EmbeddedResolutionPair.{u}) (f : EmbeddedResolutionSmoothMap A A),
    f.ambient = 𝟙 A.P → f.intrinsic = 𝟙 A.X →
      (pullback f).ambient = 𝟙 (tower A).ambient ∧
        (pullback f).intrinsic = 𝟙 (tower A).intrinsic
  pullbackComp : ∀ {A B C : EmbeddedResolutionPair.{u}}
    (f : EmbeddedResolutionSmoothMap A B) (g : EmbeddedResolutionSmoothMap B C)
    (h : EmbeddedResolutionSmoothMap A C),
    h.ambient = f.ambient ≫ g.ambient → h.intrinsic = f.intrinsic ≫ g.intrinsic →
      (pullback h).ambient = (pullback f).ambient ≫ (pullback g).ambient ∧
        (pullback h).intrinsic = (pullback f).intrinsic ≫ (pullback g).intrinsic
  intrinsic : ∀ {A B : EmbeddedResolutionPair.{u}} (e : A.X ≅ B.X),
    LabeledEmbeddedResolutionIntrinsicComparison e (tower A) (tower B)
  intrinsicId : ∀ A : EmbeddedResolutionPair.{u},
    (intrinsic (A := A) (B := A) (Iso.refl A.X)).iso = Iso.refl (tower A).intrinsic
  intrinsicComp : ∀ {A B C : EmbeddedResolutionPair.{u}} (e : A.X ≅ B.X) (f : B.X ≅ C.X),
    (intrinsic (A := A) (B := C) (e ≪≫ f)).iso =
      (intrinsic (A := A) (B := B) e).iso ≪≫ (intrinsic (A := B) (B := C) f).iso

end AlgebraicGeometry
