# AlgebraicGeometry.Scheme.NormalTowerCoverGluing

## Reason

Move the canonical chart and transport definitions and Gluing to a shared statement module
so that the separate geometric steps can import them without a cycle. Every existing name,
signature, body and structure field stays verbatim; the item publicly re-exports them.
Overlaps and Realization only separate the existing fields and contain no proof holes.

## Old

In Sheaf.AlgebraicGeometry.NormalTowerCommonLevelCoverGluing:

```lean
/-- The chart above an open of the base, with its chosen fibre product.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def chart {V : Scheme.{u}} (A : Over V) (W : V.Opens) : Scheme.{u} :=
  pullback A.hom W.ι

/-- The canonical map of charts induced by a tower map and an inclusion of base opens.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def chartMap {V : Scheme.{u}} {A B : Over V} (q : A ⟶ B)
    {T W : V.Opens} (h : T ≤ W) : chart A T ⟶ chart B W :=
  pullback.map A.hom T.ι B.hom W.ι q.left (V.homOfLE h) (𝟙 V)
    (by simp) (by simp)

/-- The inclusion from a smaller chart into a larger chart at the same tower level.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def chartInclusion {V : Scheme.{u}} (A : Over V)
    {T W : V.Opens} (h : T ≤ W) : chart A T ⟶ chart A W :=
  chartMap (𝟙 A) h

/-- The projection of a chart into an open containing its base open.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def chartToOpen {V : Scheme.{u}} (A : Over V)
    {T U : V.Opens} (h : T ≤ U) : chart A T ⟶ U.toScheme :=
  pullback.snd A.hom T.ι ≫ V.homOfLE h

/-- Transport a specified finite étale identification through a commutative square.
This is the composite of Mathlib's canonical pullback-composition and congruence
isomorphisms, not a choice of an unspecified comparison.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def pullbackIdentification
    {B C D E S : Scheme.{u}}
    (g : C ⟶ B) (i : D ⟶ B) (j : E ⟶ C) (h : E ⟶ D)
    (t : D ⟶ S) (t' : E ⟶ S) (sq : j ≫ g = h ≫ i) (ht : h ≫ t = t')
    (Y : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ B)
    (P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ S)
    (θ : (MorphismProperty.Over.pullback _ ⊤ i).obj Y ≅
      (MorphismProperty.Over.pullback _ ⊤ t).obj P) :
    (MorphismProperty.Over.pullback _ ⊤ j).obj
      ((MorphismProperty.Over.pullback _ ⊤ g).obj Y) ≅
      (MorphismProperty.Over.pullback _ ⊤ t').obj P :=
  (MorphismProperty.Over.pullbackComp j g).symm.app Y ≪≫
    (MorphismProperty.Over.pullbackCongr sq).app Y ≪≫
    (MorphismProperty.Over.pullbackComp h i).app Y ≪≫
    (MorphismProperty.Over.pullback _ ⊤ h).mapIso θ ≪≫
    (MorphismProperty.Over.pullbackComp h t).symm.app P ≪≫
    (MorphismProperty.Over.pullbackCongr ht).app P

/-- Pull the specified identification of a local cover to a tower chart above `T`.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def localIdentification {V : Scheme.{u}} {A B : Over V}
    (q : A ⟶ B) (U W T : V.Opens) (hTW : T ≤ W)
    (Y : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (chart B W))
    (P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ U.toScheme)
    (θ : (MorphismProperty.Over.pullback _ ⊤ (chartInclusion B inf_le_left)).obj Y ≅
      (MorphismProperty.Over.pullback _ ⊤
        (chartToOpen B (inf_le_right : W ⊓ U ≤ U))).obj P) :
    (MorphismProperty.Over.pullback _ ⊤
      (chartInclusion A (inf_le_left : T ⊓ U ≤ T))).obj
      ((MorphismProperty.Over.pullback _ ⊤ (chartMap q hTW)).obj Y) ≅
      (MorphismProperty.Over.pullback _ ⊤
        (chartToOpen A (inf_le_right : T ⊓ U ≤ U))).obj P :=
  pullbackIdentification (chartMap q hTW)
    (chartInclusion B (inf_le_left : W ⊓ U ≤ W))
    (chartInclusion A (inf_le_left : T ⊓ U ≤ T))
    (chartMap q (inf_le_inf hTW le_rfl))
    (chartToOpen B (inf_le_right : W ⊓ U ≤ U))
    (chartToOpen A (inf_le_right : T ⊓ U ≤ U))
    (by
      apply pullback.hom_ext <;>
        simp [chartInclusion, chartMap, Category.assoc])
    (by simp [chartMap, chartToOpen, Category.assoc]) Y P θ

/-- Restrict a global identification on `U` to the chart above `T ∩ U`.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def globalIdentification {V : Scheme.{u}} (A : Over V) (U T : V.Opens)
    (Z : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ A.left)
    (P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ U.toScheme)
    (θ : (MorphismProperty.Over.pullback _ ⊤ (pullback.fst A.hom U.ι)).obj Z ≅
      (MorphismProperty.Over.pullback _ ⊤ (pullback.snd A.hom U.ι)).obj P) :
    (MorphismProperty.Over.pullback _ ⊤
      (chartInclusion A (inf_le_left : T ⊓ U ≤ T))).obj
      ((MorphismProperty.Over.pullback _ ⊤ (pullback.fst A.hom T.ι)).obj Z) ≅
      (MorphismProperty.Over.pullback _ ⊤
        (chartToOpen A (inf_le_right : T ⊓ U ≤ U))).obj P :=
  pullbackIdentification (pullback.fst A.hom T.ι) (pullback.fst A.hom U.ι)
    (chartInclusion A (inf_le_left : T ⊓ U ≤ T))
    (chartInclusion A (inf_le_right : T ⊓ U ≤ U))
    (pullback.snd A.hom U.ι) (chartToOpen A (inf_le_right : T ⊓ U ≤ U))
    (by simp [chartInclusion, chartMap])
    (by simp [chartInclusion, chartMap, chartToOpen]) Z P θ

/-- Restrict an isomorphism between two pulled-back covers, retaining the direct
pullback models on the smaller base.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def restrictIso {B C D S : Scheme.{u}} (k : C ⟶ B)
    (f : B ⟶ D) (g : B ⟶ S) (f' : C ⟶ D) (g' : C ⟶ S)
    (hf : f' = k ≫ f) (hg : g' = k ≫ g)
    (Y : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ D)
    (Z : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ S)
    (e : (MorphismProperty.Over.pullback _ ⊤ f).obj Y ≅
      (MorphismProperty.Over.pullback _ ⊤ g).obj Z) :
    (MorphismProperty.Over.pullback _ ⊤ f').obj Y ≅
      (MorphismProperty.Over.pullback _ ⊤ g').obj Z :=
  (MorphismProperty.Over.pullbackComp k f f' hf).app Y ≪≫
    (MorphismProperty.Over.pullback _ ⊤ k).mapIso e ≪≫
    (MorphismProperty.Over.pullbackComp k g g' hg).symm.app Z

/-- Restrict a local overlap isomorphism to a smaller base open.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def restrictLocalIso {V : Scheme.{u}} {A B C : Over V}
    (q : A ⟶ B) (r : A ⟶ C) {W Q T R : V.Opens}
    (hTW : T ≤ W) (hTQ : T ≤ Q) (hRT : R ≤ T)
    (Y : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (chart B W))
    (Z : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (chart C Q))
    (e : (MorphismProperty.Over.pullback _ ⊤ (chartMap q hTW)).obj Y ≅
      (MorphismProperty.Over.pullback _ ⊤ (chartMap r hTQ)).obj Z) :
    (MorphismProperty.Over.pullback _ ⊤ (chartMap q (hRT.trans hTW))).obj Y ≅
      (MorphismProperty.Over.pullback _ ⊤ (chartMap r (hRT.trans hTQ))).obj Z :=
  restrictIso (chartInclusion A hRT) (chartMap q hTW) (chartMap r hTQ)
    (chartMap q (hRT.trans hTW)) (chartMap r (hRT.trans hTQ))
    (by apply pullback.hom_ext <;> simp [chartInclusion, chartMap, Category.assoc])
    (by apply pullback.hom_ext <;> simp [chartInclusion, chartMap, Category.assoc]) Y Z e

/-- Restrict a chart trivialization of the global cover to a smaller base open.
Source: ILO IX 2.1 (blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
noncomputable def restrictTrivialization {V : Scheme.{u}} {A B : Over V}
    (q : A ⟶ B) {W T : V.Opens} (h : T ≤ W)
    (Z : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ A.left)
    (Y : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (chart B W))
    (e : (MorphismProperty.Over.pullback _ ⊤ (pullback.fst A.hom W.ι)).obj Z ≅
      (MorphismProperty.Over.pullback _ ⊤ (chartMap q le_rfl)).obj Y) :
    (MorphismProperty.Over.pullback _ ⊤ (pullback.fst A.hom T.ι)).obj Z ≅
      (MorphismProperty.Over.pullback _ ⊤ (chartMap q h)).obj Y :=
  restrictIso (chartInclusion A h) (pullback.fst A.hom W.ι) (chartMap q le_rfl)
    (pullback.fst A.hom T.ι) (chartMap q h)
    (by simp [chartInclusion, chartMap])
    (by apply pullback.hom_ext <;> simp [chartInclusion, chartMap, Category.assoc]) Z Y e

/-- The witnesses and equations in common-level cover gluing, at a fixed common level.
The transition isomorphisms live on the actual pairwise intersections, and their
cocycle is tested on the actual triple intersections. The fields only package the
conclusion of the theorem below.
Source: ILO IX 2.1 and the DAG's explicit overlap assembly
(blueprint: lem-sfb-normal-tower-common-level-cover-gluing). -/
structure Gluing {V : Scheme.{u}} (A : Over V) (U : V.Opens)
    (P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ U.toScheme)
    {s : ℕ} (B : Fin s → Over V) (W : Fin s → V.Opens)
    (q : ∀ j : Fin s, A ⟶ B j)
    (Y : ∀ j : Fin s,
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (chart (B j) (W j)))
    (θlocal : ∀ j : Fin s,
      (MorphismProperty.Over.pullback _ ⊤
        (chartInclusion (B j) (inf_le_left : W j ⊓ U ≤ W j))).obj (Y j) ≅
      (MorphismProperty.Over.pullback _ ⊤
        (chartToOpen (B j) (inf_le_right : W j ⊓ U ≤ U))).obj P) where
  /-- The global finite étale cover. -/
  Z : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ A.left
  /-- The global identification over the prescribed open. -/
  θ : (MorphismProperty.Over.pullback _ ⊤ (pullback.fst A.hom U.ι)).obj Z ≅
    (MorphismProperty.Over.pullback _ ⊤ (pullback.snd A.hom U.ι)).obj P
  /-- The global cover restricts to the specified base changes on each chart. -/
  e : ∀ j : Fin s,
    (MorphismProperty.Over.pullback _ ⊤ (pullback.fst A.hom (W j).ι)).obj Z ≅
    (MorphismProperty.Over.pullback _ ⊤ (chartMap (q j) le_rfl)).obj (Y j)
  /-- The chart isomorphisms preserve each specified identification with `P`. -/
  identification : ∀ j : Fin s,
    (MorphismProperty.Over.pullback _ ⊤
      (chartInclusion A (inf_le_left : W j ⊓ U ≤ W j))).mapIso (e j) ≪≫
      localIdentification (q j) U (W j) (W j) le_rfl (Y j) P (θlocal j) =
        globalIdentification A U (W j) Z P θ
  /-- The overlap isomorphisms. -/
  α : ∀ i j : Fin s,
    (MorphismProperty.Over.pullback _ ⊤ (chartMap (q i) inf_le_left)).obj (Y i) ≅
    (MorphismProperty.Over.pullback _ ⊤
      (chartMap (q j) (inf_le_right : W i ⊓ W j ≤ W j))).obj (Y j)
  /-- Their restriction is exactly `θ_j⁻¹ θ_i`. -/
  overlap_identification : ∀ i j : Fin s,
    (MorphismProperty.Over.pullback _ ⊤
      (chartInclusion A (inf_le_left : (W i ⊓ W j) ⊓ U ≤ W i ⊓ W j))).mapIso
      (α i j) ≪≫
      localIdentification (q j) U (W j) (W i ⊓ W j) inf_le_right (Y j) P (θlocal j) =
      localIdentification (q i) U (W i) (W i ⊓ W j) inf_le_left (Y i) P (θlocal i)
  /-- No other overlap isomorphism has the given restriction. -/
  overlap_unique : ∀ (i j : Fin s)
    (β : (MorphismProperty.Over.pullback _ ⊤ (chartMap (q i) inf_le_left)).obj (Y i) ≅
      (MorphismProperty.Over.pullback _ ⊤
        (chartMap (q j) (inf_le_right : W i ⊓ W j ≤ W j))).obj (Y j)),
    (MorphismProperty.Over.pullback _ ⊤
      (chartInclusion A (inf_le_left : (W i ⊓ W j) ⊓ U ≤ W i ⊓ W j))).mapIso β ≪≫
      localIdentification (q j) U (W j) (W i ⊓ W j) inf_le_right (Y j) P (θlocal j) =
      localIdentification (q i) U (W i) (W i ⊓ W j) inf_le_left (Y i) P (θlocal i) →
      β = α i j
  /-- The diagonal transition is the identity, including on empty charts. -/
  identity : ∀ i : Fin s, α i i = Iso.refl _
  /-- The transition maps satisfy the cocycle equation on every triple overlap. -/
  cocycle : ∀ i j k : Fin s,
    restrictLocalIso (q i) (q j) inf_le_left inf_le_right
      (inf_le_left : (W i ⊓ W j) ⊓ W k ≤ W i ⊓ W j) (Y i) (Y j) (α i j) ≪≫
    restrictLocalIso (q j) (q k) inf_le_left inf_le_right
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (W i ⊓ W j) ⊓ W k ≤ W j ⊓ W k) (Y j) (Y k) (α j k) =
    restrictLocalIso (q i) (q k) inf_le_left inf_le_right
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (W i ⊓ W j) ⊓ W k ≤ W i ⊓ W k) (Y i) (Y k) (α i k)
  /-- The global chart isomorphisms induce precisely these transitions. -/
  induces : ∀ i j : Fin s,
    restrictTrivialization (q i) (inf_le_left : W i ⊓ W j ≤ W i) Z (Y i) (e i) ≪≫
      α i j = restrictTrivialization (q j) inf_le_right Z (Y j) (e j)

```

## New

The exact declarations above live in Sheaf.AlgebraicGeometry.NormalTowerCoverGluingData.
The original item re-exports them with:

```lean
public import Sheaf.AlgebraicGeometry.NormalTowerCoverGluingData
```

Overlaps contains the original α, overlap_identification, overlap_unique, identity and
cocycle fields. Realization contains the original Z, θ, e, identification and induces
fields, with α supplied by its Overlaps argument. Gluing is unchanged.
The main theorem's full signature is unchanged.

## Users

The read-only downstream.py search for the item, including uses of Gluing, reports zero
downstream modules and only the item itself using Gluing. A direct-import search also
finds no importers. No existing module besides the assigned item changes.
No target meaning changes and no consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NormalTowerCommonLevelCoverGluing | S4 | Same re-exported API. |
| Sheaf.AlgebraicGeometry.NormalTowerCoverGluingData | S4 (new) | Owns unchanged constructions. |
| Sheaf.AlgebraicGeometry.NormalTowerOverlapSystem | S4 (new) | Uses overlap data only. |
| Sheaf.AlgebraicGeometry.NormalTowerOverlapDescent | S4 (new) | Realizes its supplied overlaps. |

## Status

landed 20261026T082939-L-2243016 2026-10-26 (merge of deliver/S4/Sheaf.AlgebraicGeometry.NormalTowerCommonLevelCoverGluing)
