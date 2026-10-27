/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.IntrinsicLabeledResolution
import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.EmbeddedResolutionOrdinaryTower
import Sheaf.AlgebraicGeometry.IntrinsicResolutionPullbackRigidity
import Sheaf.AlgebraicGeometry.IntrinsicResolutionSmoothComparison

/-!
# From synchronized embedded resolution to intrinsic smooth comparison

Source: ILO VIII 2.1.3(ii), 2.1.9, 2.3.11--2.3.13, pp.87--88,93--94.
Conditional reduction, expanded by the DAG proof using Stacks 01V7 and 07CK
(blueprint: lem-trf-embedded-to-intrinsic-smooth-resolution).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem affine_resolution_embedding (S : RationalResolutionInput.{u})
    [IsAffine S.scheme] : Nonempty (RationalResolutionEmbedding S) := by
  have : LocallyOfFiniteType S.structureMap := S.finiteType
  obtain ⟨n, c, hc, hclosed⟩ :=
    exists_isClosedImmersion_affineSpace_of_isAffine S.structureMap
  exact ⟨{
    pair := {
      X := S.scheme
      P := 𝔸(ULift.{u} (Fin n); Spec (.of (ULift.{u} ℚ)))
      base := 𝔸(ULift.{u} (Fin n); Spec (.of (ULift.{u} ℚ))) ↘ _
      inclusion := c
      closed := hclosed
      reduced := S.reduced
      smooth := SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin n))) _
      separated := inferInstance
      finiteType := inferInstance
      quasiCompact := inferInstance }
    iso := Iso.refl _
    over := by simpa using hc }⟩

private theorem disjoint_union_resolution_embedding (n : ℕ)
    (S : Fin n → RationalResolutionInput.{u}) (affine : ∀ i, IsAffine (S i).scheme)
    (T : RationalResolutionInput.{u}) (j : ∀ i, (S i).scheme ⟶ T.scheme)
    (disjointUnion : IsColimit (Cofan.mk T.scheme j)) :
    Nonempty (RationalResolutionEmbedding T) := by
  have (i : Fin n) : IsAffine (S i).scheme := affine i
  have : IsAffine (∐ fun i : Fin n ↦ (S i).scheme) := inferInstance
  let e : T.scheme ≅ ∐ fun i : Fin n ↦ (S i).scheme :=
    disjointUnion.coconePointUniqueUpToIso (coproductIsCoproduct _)
  have : IsAffine T.scheme := .of_isIso e.hom
  exact affine_resolution_embedding T

private def change_embedding {L : Type w} [LinearOrder L]
    (E : SynchronizedEmbeddedResolution.{u, w} L) {S : RationalResolutionInput.{u}}
    {A : IntrinsicLabeledOrdinaryTower L S.scheme}
    {p : RationalResolutionEmbedding S}
    (a : IntrinsicEmbeddedResolutionIdentification A p (E.tower p.pair))
    (q : RationalResolutionEmbedding S) :
    IntrinsicEmbeddedResolutionIdentification A q (E.tower q.pair) where
  iso := a.iso ≪≫ (E.intrinsic (p.iso.symm ≪≫ q.iso)).iso
  initial := by
    change (a.iso.hom.app (op ⊥) ≫
      (E.intrinsic (p.iso.symm ≪≫ q.iso)).iso.hom.app (op ⊥)) ≫ _ = _
    have he := (E.intrinsic (p.iso.symm ≪≫ q.iso)).initial
    have ha := a.initial
    simp only [Iso.app_hom] at he ha
    rw [Category.assoc, he, ← Category.assoc, ha]
    simp [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  labels := by rw [a.labels, (E.intrinsic (p.iso.symm ≪≫ q.iso)).labels]
  centers l := by
    rw [a.centers, (E.intrinsic (p.iso.symm ≪≫ q.iso)).centers]
    simp only [NatIso.trans_app, Iso.trans_hom, Scheme.IdealSheafData.comap_comp]

private theorem change_embedding_cocycle {L : Type w} [LinearOrder L]
    (E : SynchronizedEmbeddedResolution.{u, w} L) {S : RationalResolutionInput.{u}}
    {A : IntrinsicLabeledOrdinaryTower L S.scheme}
    {r : RationalResolutionEmbedding S}
    (a : IntrinsicEmbeddedResolutionIdentification A r (E.tower r.pair))
    (p q : RationalResolutionEmbedding S) :
    (change_embedding E a p).iso ≪≫ (E.intrinsic (p.iso.symm ≪≫ q.iso)).iso =
      (change_embedding E a q).iso := by
  change (a.iso ≪≫ (E.intrinsic (r.iso.symm ≪≫ p.iso)).iso) ≪≫
    (E.intrinsic (p.iso.symm ≪≫ q.iso)).iso =
      a.iso ≪≫ (E.intrinsic (r.iso.symm ≪≫ q.iso)).iso
  rw [Iso.trans_assoc, ← E.intrinsicComp]
  have hi : (r.iso.symm ≪≫ p.iso) ≪≫ (p.iso.symm ≪≫ q.iso) = r.iso.symm ≪≫ q.iso := by
    ext
    simp [Iso.trans_hom, Iso.symm_hom]
  rw [hi]

/-- Every synchronized embedded assignment induces an intrinsic labeled ordinary
resolution on all embeddable rational inputs, with canonical cartesian smooth
comparisons and the supplied change-of-embedding cocycle. Affine inputs and finite
disjoint unions of affine inputs belong to this class, including the empty union.
The intrinsic interface keeps all center ideals and deletes exactly unit extended
ideals; its ambient compatibility concerns cartesian squares of embedded pairs.
No separatedness or constant-relative-dimension hypothesis is put on the smooth map.

Source: ILO VIII 2.1.3(ii), 2.1.9, 2.3.11--2.3.13, pp.87--88,93--94
(blueprint: lem-trf-embedded-to-intrinsic-smooth-resolution).

Proof plan (the conditional argument in the node):
1. Choose a permitted embedding of each input. The strict-transform identification
   `lemma-nagata-strict-transform-ambient-closed` makes its intrinsic diagram an
   ordinary blowup tower with the specified center ideals. The embedded assignment
   supplies finite increasing labels, coherent nonempty nowhere dense regular centers,
   a regular last level and the empty/regular length-zero cases. Its intrinsic
   comparisons transport this tower to every other embedding and give the cocycle.
2. A blowup principalizes its center (`thm-nagata-blowup-principalizes-center`). Its
   universal property (`thm-nagata-blowup-universal-property`) gives uniqueness of
   maps to that blowup over its base. Induction makes every center-preserving tower
   automorphism over the input the identity, also after open restriction.
3. For an open U of X in P use O = P minus the closed complement X minus U.
   Then U = X times_P O. The ambient open immersion is etale and smooth
   (`lem-weil-pbc-open-immersion-etale`, `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`).
   The finite-type Noetherian ambient makes O quasi-compact
   (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-weil-pbc-noetherian-open-subscheme-noetherian`); the affine-pair criterion
   `lem-weil-pbc-lft-affine-pairs` makes O finite type. Smoothness restricts by
   `lem-weil-pbc-smooth-restrict-open-subschemes`; separatedness restricts by the
   diagonal. Embedded comparison and rigidity give canonical open comparisons.
4. Cover an arbitrary smooth map by standard-smooth affine charts
   (`lem-weil-pbc-smooth-locally-standard-smooth`). Affine coordinate rings are finite
   type by `lem-weil-pbc-lft-affine-pairs`, hence quotients of finite polynomial rings
   over Q. These rings are standard smooth with zero equations
   (`def-weil-pbc-standard-smooth-algebra`), so their spectra are smooth by
   `lem-weil-pbc-standard-smooth-is-smooth` and
   `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`. This gives permitted affine
   embeddings and, by finite disjoint union, all asserted disjoint-union embeddings.
5. Lift each standard-smooth algebra through the ambient quotient using
   `lem-weil-pbc-standard-smooth-quotient-lift`, without nilpotence. The lifted
   spectrum is smooth over the ambient by the same two smoothness criteria, affine
   and finite type over Q, and smooth over Q by `lem-trf-smooth-composition`.
6. Apply the embedded comparison on each resulting cartesian smooth ambient chart,
   then the intrinsic and open identifications. These comparisons retain exactly
   the nonunit extended ideals. Rigidity removes all choices of presentations/lifts.
7. Insert identity stages in the two towers at the union of their finite labels.
   Inductively, the chart opens cover each pullback level. Equality of ideal
   subsheaves is local, so the next intrinsic ideal equals the extended target ideal
   globally; it is unit exactly when it is unit on every chart. Thus no new label
   appears and precisely the unit stages disappear.
8. At every cut the projection is a smooth base change
   (`lem-pc-proper-base-change`), hence flat (`sbc-lem-smooth-criterion`). The canonical
   flat blowup comparison (`thm-nagata-blowup-flat-base-change`,
   `def-nagata-blowup-flat-base-change-map`) gives the next cartesian level.
   Blowing up the unit ideal is the identity (its Rees algebra is O[t]).
9. Rigidity identifies the resulting comparison with every local or supplied
   cartesian embedded comparison. Therefore ideals and maps are independent of
   charts and lifts. Identities and compositions have the same ideals and maps.
   Only affine neighbourhoods were used: neither separation nor a constant relative
   dimension of the smooth map is required.
-/
theorem exists_intrinsic_resolution_of_embedded (L : Type w) [LinearOrder L]
    (E : SynchronizedEmbeddedResolution.{u, w} L) :
    (∀ (S : RationalResolutionInput.{u}) [IsAffine S.scheme],
      Nonempty (RationalResolutionEmbedding S)) ∧
    (∀ (n : ℕ) (S : Fin n → RationalResolutionInput.{u})
      (_affine : ∀ i, IsAffine (S i).scheme) (T : RationalResolutionInput.{u})
      (j : ∀ i, (S i).scheme ⟶ T.scheme)
      (_disjointUnion : IsColimit (Cofan.mk T.scheme j)),
      Nonempty (RationalResolutionEmbedding T)) ∧
    Nonempty (IntrinsicResolutionOfEmbedded L E) := by
  classical
  refine ⟨affine_resolution_embedding, disjoint_union_resolution_embedding, ?_⟩
  let p (S : EmbeddableResolutionInput.{u}) : RationalResolutionEmbedding S.val :=
    Classical.choice S.property
  choose tower identified using fun S : EmbeddableResolutionInput.{u} ↦
    exists_ordinary_tower_of_embedded S.val (p S) (E.tower (p S).pair)
  let initial (S : EmbeddableResolutionInput.{u}) := Classical.choice (identified S)
  let embedding (S : EmbeddableResolutionInput.{u}) (q : RationalResolutionEmbedding S.val) :=
    change_embedding E (initial S) q
  have smoothComparison (S T : EmbeddableResolutionInput.{u})
      (h : T.val.scheme ⟶ S.val.scheme)
      (over : h ≫ S.val.structureMap = T.val.structureMap) [Smooth h] :=
    exists_intrinsic_smooth_comparison E S T (tower S) (tower T)
      (embedding S) (embedding T) h over
  refine ⟨{
    tower := tower
    embedding := embedding
    cocycle := fun S q r ↦ change_embedding_cocycle E (initial S) q r
    comparison := fun S T h over ↦ (smoothComparison S T h over).choose
    unique := ?_
    ambient := ?_ }⟩
  · intro S T h over _ c
    exact (intrinsic_resolution_pullback_subsingleton h (tower S) (tower T)).elim _ _
  · intro S T q r h over _ f hf
    exact (smoothComparison S T h over).choose_spec q r f hf

end AlgebraicGeometry
