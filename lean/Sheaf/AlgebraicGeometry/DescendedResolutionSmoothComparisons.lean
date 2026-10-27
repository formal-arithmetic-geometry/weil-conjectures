/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.AlgebraicGeometry.LabeledOrdinaryResolutionDescentData
import Sheaf.AlgebraicGeometry.AffineCoverOrdinaryResolutionComparison
import Sheaf.AlgebraicGeometry.OrdinaryResolutionLevelMapRigidity
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Descent of smooth comparisons for ordinary resolution towers

Source: ILO, Travaux de Gabber, VIII 2.1.9, 2.3.4--2.3.5(i)--(ii), pp.88,91--92
(blueprint: lem-trf-descended-resolution-smooth-comparisons).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.OrdinaryResolutionDescent

@[reassoc]
private theorem tower_toBase_transition {S : Scheme.{u}} (A : OrdinaryBlowupTower S)
    (i j : Fin (A.length + 1)) (hij : i ≤ j) :
    A.transition i j hij ≫ A.toBase i = A.toBase j := by
  simp only [OrdinaryBlowupTower.toBase, ← Category.assoc, A.transition_comp]

private theorem comparison_count_determined {n m : ℕ}
    (r : Fin m ↪o Fin n) (c d : Fin (n + 1) → Fin (m + 1))
    (hc0 : c 0 = 0) (hd0 : d 0 = 0)
    (hca : ∀ k, c (r k).succ = k.succ) (hda : ∀ k, d (r k).succ = k.succ)
    (hcd : ∀ i, i ∉ Set.range r → c i.succ = c i.castSucc)
    (hdd : ∀ i, i ∉ Set.range r → d i.succ = d i.castSucc) : c = d := by
  funext i
  induction i using Fin.induction with
  | zero => exact hc0.trans hd0.symm
  | succ i ih =>
    by_cases hi : i ∈ Set.range r
    · obtain ⟨k, rfl⟩ := hi
      exact (hca k).trans (hda k).symm
    · exact (hcd i hi).trans (ih.trans (hdd i hi).symm)

private theorem comparison_identity_retained {L : Type w} [LinearOrder L]
    {S : Scheme.{u}} (A : LabeledTower L S) (c : Comparison (𝟙 S) A A) (k) :
    c.retainedStage k = k := by
  exact A.labels.injective (c.labels_eq k).symm

private theorem comparison_composition_retained {L : Type w} [LinearOrder L]
    {S T Z : Scheme.{u}} {h : T ⟶ S} {g : Z ⟶ T}
    {A : LabeledTower L S} {B : LabeledTower L T} {C : LabeledTower L Z}
    (a : Comparison h A B) (b : Comparison g B C) (c : Comparison (g ≫ h) A C) (k) :
    c.retainedStage k = a.retainedStage (b.retainedStage k) := by
  apply A.labels.injective
  exact (c.labels_eq k).symm.trans ((b.labels_eq k).trans (a.labels_eq _))

private theorem comparison_identity_count {L : Type w} [LinearOrder L]
    {S : Scheme.{u}} (A : LabeledTower L S) (c : Comparison (𝟙 S) A A) (i) :
    c.count i = i := by
  induction i using Fin.cases with
  | zero => exact c.count_zero
  | succ k =>
    simpa only [comparison_identity_retained A c k] using c.count_after k

private theorem comparison_composition_count {L : Type w} [LinearOrder L]
    {S T Z : Scheme.{u}} {h : T ⟶ S} {g : Z ⟶ T}
    {A : LabeledTower L S} {B : LabeledTower L T} {C : LabeledTower L Z}
    (a : Comparison h A B) (b : Comparison g B C) (c : Comparison (g ≫ h) A C) (i) :
    c.count i = b.count (a.count i) := by
  have he := comparison_composition_retained a b c
  have hzero : b.count (a.count 0) = 0 := by
    have ha0 : a.count 0 = 0 := a.count_zero
    rw [ha0]
    exact b.count_zero
  have hafter : ∀ k, b.count (a.count (c.retainedStage k).succ) = k.succ := by
    intro k
    rw [he, a.count_after, b.count_after]
  have hdeleted : ∀ j, j ∉ Set.range c.retainedStage →
      b.count (a.count j.succ) = b.count (a.count j.castSucc) := by
    intro j hj
    by_cases ha : j ∈ Set.range a.retainedStage
    · obtain ⟨k, rfl⟩ := ha
      rw [a.count_after, a.count_before]
      apply b.deleted_level
      rintro ⟨l, rfl⟩
      exact hj ⟨l, he l⟩
    · rw [a.deleted_level j ha]
  exact congrFun (comparison_count_determined c.retainedStage c.count
    (fun j ↦ b.count (a.count j)) c.count_zero hzero c.count_after hafter
    c.deleted_level hdeleted) i

private theorem regularTower_empty_length {S : Scheme.{u}} (A : OrdinaryBlowupTower S)
    (hA : A.IsRegularResolution) (hS : IsEmpty S) : A.length = 0 := by
  by_contra hn
  have hp : 0 < A.length := Nat.pos_of_ne_zero hn
  obtain ⟨x, _⟩ := (hA.1 ⟨0, hp⟩).2.1
  exact hS.false (A.toBase (⟨0, hp⟩ : Fin A.length).castSucc x)


@[reassoc]
private theorem tower_toBase_transport {S : Scheme.{u}} (A : OrdinaryBlowupTower S)
    {i j : Fin (A.length + 1)} (e : i = j) :
    eqToHom (congrArg A.level e) ≫ A.toBase j = A.toBase i := by
  subst e
  simp

private theorem tower_blowup_toBase {S : Scheme.{u}} (A : OrdinaryBlowupTower S)
    (i : Fin A.length) :
    (A.blowupIso i).inv ≫ A.toBase i.succ =
      (A.center i).blowupMap ≫ A.toBase i.castSucc := by
  rw [← tower_toBase_transition A i.castSucc i.succ (le_of_lt i.castSucc_lt_succ),
    ← A.blowup_fac]
  simp

private theorem comparison_identity_map {L : Type w} [LinearOrder L]
    (S : RationalResolutionInput.{u}) (A : LabeledTower L S.scheme)
    (c : Comparison (𝟙 S.scheme) A A) (i) :
    eqToHom (congrArg A.tower.level (comparison_identity_count A c i).symm) ≫
      c.levelMap i = 𝟙 (A.tower.level i) := by
  have he := smoothComparison_levelMap_unique S S (𝟙 S.scheme) A A c i
    (eqToHom (congrArg A.tower.level (comparison_identity_count A c i)))
    (by simpa using tower_toBase_transport A.tower (comparison_identity_count A c i))
  rw [← he]
  simp

private theorem comparison_composition_map {L : Type w} [LinearOrder L]
    (S T Z : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (g : Z.scheme ⟶ T.scheme) [Smooth h] [Smooth g]
    (A : LabeledTower L S.scheme) (B : LabeledTower L T.scheme)
    (C : LabeledTower L Z.scheme)
    (a : Comparison h A B) (b : Comparison g B C) (c : Comparison (g ≫ h) A C) (i) :
    eqToHom (congrArg C.tower.level (comparison_composition_count a b c i)) ≫
      b.levelMap (a.count i) ≫ a.levelMap i = c.levelMap i := by
  apply smoothComparison_levelMap_unique S Z (g ≫ h) A C c i
  rw [Category.assoc, Category.assoc, (a.cartesian i).w,
    ← Category.assoc (b.levelMap _), (b.cartesian _).w]
  simp only [← Category.assoc]
  rw [tower_toBase_transport C.tower (comparison_composition_count a b c i)]

private theorem comparison_surjective {L : Type w} [LinearOrder L]
    {S T : Scheme.{u}} (h : T ⟶ S) [Surjective h]
    (A : LabeledTower L S) (B : LabeledTower L T) (c : Comparison h A B) :
    Function.Surjective c.retainedStage := by
  intro i
  by_contra hi
  have hunit := (c.deleted_iff_unit i).mp hi
  obtain ⟨x, hx⟩ := (A.regular.1 i).2.1
  have hs : Surjective (c.levelMap i.castSucc) :=
    MorphismProperty.of_isPullback (c.cartesian i.castSucc).flip inferInstance
  obtain ⟨y, hy⟩ := (c.levelMap i.castSucc).surjective x
  have hmem : y ∈ ((A.tower.center i).comap (c.levelMap i.castSucc)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change c.levelMap i.castSucc y ∈ (A.tower.center i).support
    rwa [hy]
  rw [hunit, Scheme.IdealSheafData.support_top] at hmem
  exact hmem

private theorem comparison_deleted_locally {L : Type w} [LinearOrder L]
    (S T : RationalResolutionInput.{u}) (D : Datum.{u, w} L)
    (h : T.scheme ⟶ S.scheme) (c : Comparison h (D.tower S) (D.tower T))
    (V : AffineCover T) (i : Fin (D.tower S).tower.length) :
    i ∉ Set.range c.retainedStage ↔
      ∀ b, ((D.tower S).tower.center i).comap
        (pullback.fst ((D.tower T).tower.toBase (c.count i.castSucc)) (V.cover.f b) ≫
          c.levelMap i.castSucc) = ⊤ := by
  rw [c.deleted_iff_unit]
  constructor
  · intro hi b
    rw [Scheme.IdealSheafData.comap_comp, hi, Scheme.IdealSheafData.comap_top]
  · intro hv
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    apply SetLike.coe_injective
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨y, hy⟩ := V.cover.covers ((D.tower T).tower.toBase (c.count i.castSucc) x)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (D.tower T).tower.toBase (c.count i.castSucc))
      (g := V.cover.f (V.cover.idx ((D.tower T).tower.toBase (c.count i.castSucc) x)))
      x y hy.symm
    have hm : z ∈ (((D.tower S).tower.center i).comap
        (pullback.fst ((D.tower T).tower.toBase (c.count i.castSucc))
          (V.cover.f _) ≫ c.levelMap i.castSucc)).support := by
      rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.support_comap]
      change (pullback.fst ((D.tower T).tower.toBase (c.count i.castSucc))
        (V.cover.f _)) z ∈
        (((D.tower S).tower.center i).comap (c.levelMap i.castSucc)).support
      rwa [hz]
    rw [hv _, Scheme.IdealSheafData.support_top] at hm
    exact hm

private theorem comparison_canonical_steps {L : Type w} [LinearOrder L]
    (S T : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme) [Smooth h]
    (A : LabeledTower L S.scheme) (B : LabeledTower L T.scheme)
    (c : Comparison h A B) : CanonicalSteps c := by
  intro k f hf _ e he
  let rhs := (B.tower.blowupIso k).hom ≫ e.hom ≫
    ((A.tower.center (c.retainedStage k)).blowupFlatBaseChangeIso f).hom ≫
      pullback.fst _ _ ≫ (A.tower.blowupIso (c.retainedStage k)).inv
  have hbl : rhs ≫ A.tower.toBase (c.retainedStage k).succ =
      B.tower.toBase k.succ ≫ h := by
    dsimp only [rhs]
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      tower_blowup_toBase, ← Category.assoc (pullback.fst _ _), pullback.condition,
      Category.assoc, ← Category.assoc
        (((A.tower.center (c.retainedStage k)).blowupFlatBaseChangeIso f).hom),
      Scheme.IdealSheafData.blowupFlatBaseChangeIso_hom_snd]
    rw [← Category.assoc e.hom, he, hf]
    rw [Category.assoc, (c.cartesian _).w,
      tower_toBase_transport_assoc B.tower (c.count_before k).symm,
      ← Category.assoc, B.tower.blowup_fac, tower_toBase_transition_assoc]
  have hu := smoothComparison_levelMap_unique S T h A B c (c.retainedStage k).succ
    (eqToHom (congrArg B.tower.level (c.count_after k)) ≫ rhs) (by
      rw [Category.assoc, hbl, ← Category.assoc,
        tower_toBase_transport B.tower (c.count_after k)])
  rw [← hu]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  dsimp only [rhs]
  simp only [Category.assoc]

/-- Smooth comparisons descend canonically from the specified affine-cover comparisons,
with all ordered contractions, level maps, extended ideals and chart normalizations.
Source: ILO VIII 2.1.9,2.3.4--2.3.5(i)--(ii)
(blueprint: lem-trf-descended-resolution-smooth-comparisons).

Proof:
1. Smoothness implies flatness by `sbc-lem-smooth-criterion`; flatness persists under
base change (`lem-weil-pbc-flat-morphism-base-change`). Inductively apply
`thm-nagata-blowup-flat-base-change` at each level. The fibre-product universal property
(`def-pc-fibre-product`) identifies the result with the uncontracted cartesian tower;
its center ideals are exactly `def-nagata-extended-ideal`.
2. On affine blowup charts the canonical map sends c tensor (x/a) to c times phi(x)/phi(a).
The coefficient-and-fraction formula in `lem-sfb-flat-pullback-blowup-chart-restrictions`
commutes with restriction, identity and iterated tensor base change. The unit center has
the chart at 1 and gives the identity. Scheme morphism gluing
(`lem-weil-pbc-scheme-morphism-gluing`) makes these equalities global.
3. Choose finite affine covers of the target and source, the latter subordinate to the
inverse images of the former. Quasi-compactness gives finite refinements
(`def-weil-finite-type-morphism`). Smooth restriction to opens and locality on the
source (`lem-weil-pbc-smooth-restrict-open-subschemes`, `lem-weil-pbc-smooth-local-on-source`)
give a smooth map of their whole disjoint unions. Apply the specified local comparison
and the uncontracted cover identifications. Its one ordered survivor embedding and count
synchronize all components; insert unit stages on components where a label is absent.
4. At each original level the local isomorphisms agree on overlaps. Cover an overlap by
affine source opens mapping into affine target opens in the target overlap; do not assume
intersections affine. The prescribed cocycle identifies ideals. Inductively the maps at
the next level agree by the formula in step 2, or by the unit identity. Glue the maps and
their inverses using `lem-weil-pbc-scheme-morphism-gluing`.
5. The glued maps commute with every transition, and each retained center is the extended
ideal. A label is deleted exactly when the extended ideal is unit on every lifted source
chart, since equality of ideal sheaves is local. This gives the global comparison of
`def-trf-ordinary-resolution-rule`, including its cartesian squares and count equations.
6. Compare any two subordinate covers on a common affine refinement. The cover cocycle
and step 2 give the same ideals, unit predicates and level maps at each original stage.
Gluing uniqueness proves cover independence, and proves restriction to every specified
local comparison. The canonical step equation is exactly flat blowup base change, hence
the tensor identification on every affine blowup chart.
7. For the identity, no nonempty center becomes unit. Thus all stages survive, both
index maps are identities and the level maps are identities by step 2 and gluing.
8. For a composite, extension of ideals twice is direct extension
(`def-nagata-extended-ideal`, `def-pc-fibre-product`), and a unit ideal stays unit.
Consequently the survivor embeddings compose and the direct count is the composite
count. The successive and direct chart formulas in step 2 agree under canonical tensor
associativity, so gluing gives the stated equation for level maps with index transports.
9. Surjective base change (`lem-weil-pbc-surjective-base-change`) meets every nonempty
center, so no extended ideal is unit and no stage is deleted. The argument uses neither
constant relative dimension nor connectedness. All disjoint unions were whole inputs.
For the empty scheme the empty affine cover gives the specified uncontracted comparison
with the local algorithm; if that tower is trivial, the global tower is trivial. -/
theorem descendedResolution_smoothComparisons
    (L : Type w) [LinearOrder L] (D : Datum.{u, w} L) :
    Nonempty (DescendedRule D) := by
  classical
  have existsComparison := fun (S T : RationalResolutionInput.{u})
    (h : T.scheme ⟶ S.scheme) (over : h ≫ S.structureMap = T.structureMap)
    (_ : Smooth h) ↦ affineCover_ordinaryResolution_comparison D S T h over
  choose c hc using existsComparison
  let F : SmoothFunctorialOrdinaryResolution.{u} := {
    tower := fun S ↦ (D.tower S).tower
    resolves := fun S ↦ (D.tower S).regular
    comparison := fun S T h over _ ↦ (c S T h over inferInstance).toOrdinaryResolutionComparison
    identity_count := fun S i ↦ comparison_identity_count (D.tower S)
      (c S S (𝟙 S.scheme) (by simp) inferInstance) i
    identity_map := fun S i ↦ comparison_identity_map S (D.tower S)
      (c S S (𝟙 S.scheme) (by simp) inferInstance) i
    composition_count := fun S T Z h g overH overG _ _ i ↦ comparison_composition_count
      (c S T h overH inferInstance) (c T Z g overG inferInstance)
      (c S Z (g ≫ h) (by rw [Category.assoc, overH, overG]) inferInstance) i
    composition_map := fun S T Z h g overH overG _ _ i ↦ comparison_composition_map S T Z h g
      (D.tower S) (D.tower T) (D.tower Z)
      (c S T h overH inferInstance) (c T Z g overG inferInstance)
      (c S Z (g ≫ h) (by rw [Category.assoc, overH, overG]) inferInstance) i
    surjective_no_deletion := fun S T h over _ _ ↦ comparison_surjective h
      (D.tower S) (D.tower T) (c S T h over inferInstance)
  }
  let G : GlobalRule D := {
    rule := F
    tower_eq := fun _ ↦ rfl
    labels_eq := fun S T h over _ k ↦ (c S T h over inferInstance).labels_eq k
  }
  exact ⟨{
    toGlobalRule := G
    restricts := fun S T h over _ U V v square overV _ ↦
      hc S T h over inferInstance U V v square overV
    deleted_locally := fun S T h over _ V i ↦
      comparison_deleted_locally S T D h (c S T h over inferInstance) V i
    identity_retained := fun S k ↦
      comparison_identity_retained (D.tower S) (c S S (𝟙 S.scheme) (by simp) inferInstance) k
    composition_retained := fun S T Z h g overH overG _ _ k ↦
      comparison_composition_retained
        (c S T h overH inferInstance) (c T Z g overG inferInstance)
        (c S Z (g ≫ h) (by rw [Category.assoc, overH, overG]) inferInstance) k
    canonical_steps := fun S T h over _ ↦ comparison_canonical_steps S T h
      (D.tower S) (D.tower T) (c S T h over inferInstance)
    empty_trivial := fun S _ hS _ ↦ regularTower_empty_length
      (D.tower S).tower (D.tower S).regular hS
  }⟩

end AlgebraicGeometry.OrdinaryResolutionDescent
