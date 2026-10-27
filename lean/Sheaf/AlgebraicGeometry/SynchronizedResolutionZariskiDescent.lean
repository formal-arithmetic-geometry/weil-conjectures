/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.LabeledOrdinaryZariskiResolutionData
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.BlowupUniversal

import Sheaf.AlgebraicGeometry.OrdinaryResolutionPaddedOverlaps
import Sheaf.AlgebraicGeometry.AffineResolutionDescentExistence
import Sheaf.AlgebraicGeometry.AffineResolutionDescentComparison
import Sheaf.AlgebraicGeometry.EmbeddedResolutionAffineDescent

/-! # Synchronized ordinary resolution descends through affine covers

Source: ILO, Travaux de Gabber, VIII 2.1.9, 2.3.1 and Remark 2.3.5(ii),
printed pp.88,91--92; the conditional ordinary-tower expansion of the synchronization
argument (blueprint: lem-trf-synchronized-resolution-zariski-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem ordinary_tower_maps_ext {X Y : Scheme.{u}}
    (A : OrdinaryBlowupTower X) (B : OrdinaryBlowupTower Y) (e : B.length = A.length)
    (f g : ∀ i : Fin (B.length + 1),
      B.level i ⟶ A.level (Fin.cast (congrArg Nat.succ e) i))
    (hzero : f 0 = g 0)
    (hf : ∀ i : Fin B.length,
      B.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ) ≫ f i.castSucc =
        f i.succ ≫ A.transition (Fin.cast e i).castSucc
          (Fin.cast e i).succ (le_of_lt (Fin.cast e i).castSucc_lt_succ))
    (hg : ∀ i : Fin B.length,
      B.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ) ≫ g i.castSucc =
        g i.succ ≫ A.transition (Fin.cast e i).castSucc
          (Fin.cast e i).succ (le_of_lt (Fin.cast e i).castSucc_lt_succ))
    (hc : ∀ i : Fin B.length,
      B.center i = (A.center (Fin.cast e i)).comap (f i.castSucc)) : f = g := by
  rcases A with ⟨n, XA, a0, ta, tai, tac, IA, ba, bfa⟩
  rcases B with ⟨m, XB, b0, tb, tbi, tbc, IB, bb, bfb⟩
  dsimp only at e
  subst m
  dsimp only at f g hzero hf hg hc
  simp only [Fin.cast_eq_self] at f g hf hg hc
  funext i
  induction i using Fin.induction with
  | zero => exact hzero
  | succ i ih =>
    apply (cancel_mono (ba i).hom).mp
    apply (IA i).hom_ext_of_isInvertible_comap
      (t := tb i.castSucc i.succ (le_of_lt i.castSucc_lt_succ) ≫ f i.castSucc)
    · rw [Scheme.IdealSheafData.comap_comp, ← hc i, ← bfb i,
        Scheme.IdealSheafData.comap_comp]
      exact (IB i).isInvertible_comap_blowupMap.comap_of_flat (bb i).hom
    · rw [Category.assoc, bfa i, ← hf i]
    · rw [Category.assoc, bfa i, ← hg i, ih]

private theorem labeled_cartesian_maps_subsingleton {L : Type w} [LinearOrder L]
    {X Y : Scheme.{u}} (h : Y ⟶ X)
    (A : LabeledOrdinaryTower L X) (B : LabeledOrdinaryTower L Y) :
    Subsingleton (LabeledOrdinaryCartesianMap h A B) := by
  constructor
  intro c d
  have hm : c.map = d.map := by
    apply ordinary_tower_maps_ext A.tower B.tower c.length_eq c.map d.map
    · apply (cancel_mono A.tower.initial.hom).mp
      have hc := (c.cartesian 0).w
      have hd := (d.cartesian 0).w
      simpa [OrdinaryBlowupTower.toBase, A.tower.transition_id, B.tower.transition_id]
        using hc.trans hd.symm
    · exact c.arrows
    · exact d.arrows
    · exact c.centers
  cases c with
  | mk c cl =>
    cases d with
    | mk d dl =>
      cases c with
      | mk ce cm cp ca cc =>
        cases d with
        | mk de dm dp da dc =>
          dsimp only at hm
          cases hm
          rfl

private theorem labeled_cartesian_label_range {L : Type w} [LinearOrder L]
    {X Y : Scheme.{u}} {h : Y ⟶ X}
    {A : LabeledOrdinaryTower L X} {B : LabeledOrdinaryTower L Y}
    (c : LabeledOrdinaryCartesianMap h A B) : Set.range B.label = Set.range A.label := by
  ext l
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast c.length_eq i, (c.labels i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast c.length_eq.symm i, ?_⟩
    simpa using c.labels (Fin.cast c.length_eq.symm i)

private theorem labeled_cartesian_maps_composite {L : Type w} [LinearOrder L]
    {X : Scheme.{u}} (B C D : LabeledOrdinaryTower L X)
    (bc : LabeledOrdinaryCartesianMap (𝟙 X) B C)
    (cd : LabeledOrdinaryCartesianMap (𝟙 X) C D)
    (bd : LabeledOrdinaryCartesianMap (𝟙 X) B D) : bc.IsComposite cd bd := by
  rcases B with ⟨⟨n, XB, b0, tb, tbi, tbc, IB, bb, bfb⟩, lb⟩
  rcases C with ⟨⟨m, XC, c0, tc, tci, tcc, IC, cb, cfb⟩, lc⟩
  rcases D with ⟨⟨k, XD, d0, td, tdi, tdc, ID, db, dfb⟩, ld⟩
  have hmn : m = n := bc.length_eq
  have hkm : k = m := cd.length_eq
  subst m
  subst k
  rcases bc with ⟨⟨ebc, fbc, pbc, abc, ibc⟩, lbc⟩
  rcases cd with ⟨⟨ecd, fcd, pcd, acd, icd⟩, lcd⟩
  rcases bd with ⟨⟨ebd, fbd, pbd, abd, ibd⟩, lbd⟩
  dsimp only at fbc fcd fbd abc acd abd ibc icd
  simp only [Fin.cast_eq_self] at fbc fcd fbd abc acd abd ibc icd
  have hm := ordinary_tower_maps_ext
    (OrdinaryBlowupTower.mk n XB b0 tb tbi tbc IB bb bfb)
    (OrdinaryBlowupTower.mk n XD d0 td tdi tdc ID db dfb) rfl
    (fun i ↦ fcd i ≫ fbc i) fbd
  dsimp only at hm
  simp only [Fin.cast_eq_self] at hm
  have he : (fun i ↦ fcd i ≫ fbc i) = fbd := by
    apply hm
    · apply (cancel_mono b0.hom).mp
      have hbc := (pbc 0).w
      have hcd := (pcd 0).w
      have hbd := (pbd 0).w
      change fbc 0 ≫ (tb 0 0 le_rfl ≫ b0.hom) =
        (tc 0 0 le_rfl ≫ c0.hom) ≫ 𝟙 X at hbc
      change fcd 0 ≫ (tc 0 0 le_rfl ≫ c0.hom) =
        (td 0 0 le_rfl ≫ d0.hom) ≫ 𝟙 X at hcd
      change fbd 0 ≫ (tb 0 0 le_rfl ≫ b0.hom) =
        (td 0 0 le_rfl ≫ d0.hom) ≫ 𝟙 X at hbd
      simp only [tbi, tci, tdi, Category.id_comp, Category.comp_id] at hbc hcd hbd
      rw [Category.assoc, hbc, hcd, hbd]
    · intro i
      simpa only [Category.assoc] using
        (congrArg (fun f ↦ f ≫ fbc i.castSucc) (acd i)).trans
          (by rw [Category.assoc, abc i])
    · exact abd
    · intro i
      rw [Scheme.IdealSheafData.comap_comp, ← ibc i, ← icd i]
  intro i
  exact congrFun he i

/-- A labeled open-functorial ordinary resolution rule extends uniquely through Zariski
synchronization to all reduced finite-type rational schemes, without separation.

Source: ILO VIII 2.1.9, 2.3.1 and Remark 2.3.5(ii), printed pp.88,91--92
(blueprint: lem-trf-synchronized-resolution-zariski-descent).

Proof (the accepted DAG expansion, with ordinary, not normalized, blowups):
1. Finite type over the Noetherian rational field gives a Noetherian input, by
   lem-weil-pbc-finite-type-over-noetherian. Its opens are Noetherian and quasi-compact
   (lem-weil-pbc-noetherian-open-subscheme-noetherian), so open immersions are finite type
   (lem-weil-pbc-qc-open-immersion-finite-type). Use finite-type composition/base change
   (lem-sfb-finite-type-composition-base-change) and a finite affine cover
   (lem-pqf-finite-affine-cover-qc-open), including the empty cover.
2. Affine charts are reduced; their finite-type coordinate algebras
   (lem-pc-affine-finite-type-algebra) present them as closed subschemes of affine spaces.
   These ambients are smooth (sbc-lem-affine-space-smooth), separated
   (lem-weil-pbc-affine-source-morphism-separated) and finite type. Finite disjoint unions
   of these inputs therefore lie in the embedded class.
3. Open immersions are flat (def-weil-flat-morphism). Pull back each ordinary blowup
   by thm-nagata-blowup-flat-base-change with the actual extended ideal and canonical
   map of def-nagata-blowup-flat-base-change-map. Unit ideals give identity blowups by
   thm-nagata-global-blowup-complement. Restore those stages at their original labels.
   A proper ideal is retained even when its blowup map is an isomorphism.
4. On affine overlaps both padded restrictions contract to the same A(W). Refine
   intersections by lem-weil-pbc-affine-opens-basis. The comparisons agree on refinements
   and triple overlaps: thm-nagata-blowup-principalizes-center and the uniqueness in
   thm-nagata-blowup-universal-property identify them with the canonical comparison
   of prop-nagata-global-blowup-cover-independent.
5. Descend the ideal sectionwise: a section belongs exactly when all its chart
   restrictions belong to the local ideals. The sheaf condition gives a unique ideal
   with those restrictions. Quasi-coherence, finite type and finite-type kernels are
   local, giving coherence by pqf-def-coherent, also on unit-ideal charts.
6. Blow up this global ideal, using def-nagata-global-blowup; flat base change identifies
   its chart restrictions with the next levels. Induct through the finite label list.
   Properness (thm-nagata-global-blowup-proper) gives finite type of each transition
   (def-weil-proper-morphism), hence of every level by finite-type composition.
7. A center is nonempty because its disjoint-union pullback is nonempty, has empty
   interior because this holds on the covering opens, and is regular by the local-ring
   criterion def-weil-regular-scheme. The same criterion proves regularity of the last
   level. Empty chart pieces do not affect the argument.
8. Compare two covers with their combined family. If one subcover lost a label,
   every affine overlap with the other subcover would have unit ideal at that label.
   Such overlaps cover the other family, so its ideal would be a unit everywhere on
   the combined tower, contradicting the nonempty center. Neither subcover loses a label.
9. Unique ideal descent and the canonical ordinary blowup comparison identify the
   three constructions, preserving labels and ideals. For three covers use their
   combined family and uniqueness of blowup lifts to obtain transitivity.
10. For an embedded input the union of chart-label sets is exactly its label set,
    since otherwise a center would be empty. The same descent recovers A itself.
    Any other cover construction has the same descended ideals and blowups, giving
    the unique cartesian comparison over the identity. Such comparisons have
    isomorphisms as all level maps; their uniqueness implies all cover cocycles.
    For the empty input the assigned disjoint-union tower has length zero.
-/
theorem exists_synchronized_resolution_zariski_descent (L : Type w) [LinearOrder L]
    (A : OrdinaryZariskiResolutionRule.{u, w} L) :
    ∃ R : ∀ S : RationalResolutionInput.{u}, LabeledOrdinaryTower L S.scheme,
      (∀ S, (R S).IsResolution) ∧
      (∀ S, IsEmpty S.scheme → (R S).tower.length = 0) ∧
      (∀ (S : RationalResolutionInput.{u}) (hS : S.IsEmbeddable),
        Nonempty (Unique (LabeledOrdinaryCartesianMap (𝟙 S.scheme) (R S) (A.tower S hS)))) ∧
      (∀ S, A.IsSynchronizedDescent S (R S)) ∧
      A.HasPaddedOverlaps ∧
      (∀ (S T V : RationalResolutionInput.{u})
        (q : T.scheme ⟶ S.scheme) (r : V.scheme ⟶ S.scheme),
        ResolutionAffineCover S T q → ResolutionAffineCover S V r →
        ∃ (hT : T.IsEmbeddable) (hV : V.IsEmbeddable),
          Set.range (A.tower T hT).label = Set.range (A.tower V hV).label) ∧
      (∀ (S : RationalResolutionInput.{u}) (B : LabeledOrdinaryTower L S.scheme),
        A.IsAffineDescent S B →
          Nonempty (Unique (LabeledOrdinaryCartesianMap (𝟙 S.scheme) (R S) B))) ∧
      (∀ (S : RationalResolutionInput.{u}) (B C D : LabeledOrdinaryTower L S.scheme),
        A.IsAffineDescent S B → A.IsAffineDescent S C → A.IsAffineDescent S D →
        ∀ (bc : LabeledOrdinaryCartesianMap (𝟙 S.scheme) B C)
          (cd : LabeledOrdinaryCartesianMap (𝟙 S.scheme) C D)
          (bd : LabeledOrdinaryCartesianMap (𝟙 S.scheme) B D), bc.IsComposite cd bd) := by
  classical
  have hpad := ordinary_resolution_padded_overlaps A
  choose R hR hdesc using exists_affine_resolution_descent A hpad
  have hcompare (S : RationalResolutionInput.{u}) :=
    affine_resolution_descent_comparison A hpad S (R S) (hdesc S)
  have hunique (S : RationalResolutionInput.{u}) (B : LabeledOrdinaryTower L S.scheme)
      (hB : A.IsAffineDescent S B) :
      Nonempty (Unique (LabeledOrdinaryCartesianMap (𝟙 S.scheme) (R S) B)) := by
    obtain ⟨c⟩ := (hcompare S).2 B hB
    exact ⟨{ default := c, uniq := fun d ↦
      (labeled_cartesian_maps_subsingleton (𝟙 S.scheme) (R S) B).elim d c }⟩
  refine ⟨R, hR, ?_, ?_, ?_, hpad, ?_, hunique, ?_⟩
  · intro S hS
    obtain ⟨T, q, _, hT, ⟨c⟩⟩ := hdesc S
    have : IsEmpty S.scheme := hS
    have : IsEmpty T.scheme := Function.isEmpty q
    exact c.length_eq.symm.trans (A.empty T hT inferInstance)
  · intro S hS
    exact hunique S (A.tower S hS) (embedded_resolution_isAffineDescent A hpad S hS)
  · intro S T q cover
    obtain ⟨hT, c, hc⟩ := (hcompare S).1 T q cover
    exact ⟨hT, c, hc, fun d _ ↦
      (labeled_cartesian_maps_subsingleton q (R S) (A.tower T hT)).elim d c⟩
  · intro S T V q r coverT coverV
    obtain ⟨hT, c, _⟩ := (hcompare S).1 T q coverT
    obtain ⟨hV, d, _⟩ := (hcompare S).1 V r coverV
    exact ⟨hT, hV, (labeled_cartesian_label_range c).trans
      (labeled_cartesian_label_range d).symm⟩
  · intro S B C D _ _ _ bc cd bd
    exact labeled_cartesian_maps_composite B C D bc cd bd

end AlgebraicGeometry
