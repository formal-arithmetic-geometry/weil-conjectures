/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite

/-!
# Finite affine component subatlases

Source: Stacks Project, Properties of Spaces, Tag 03E4 (lemma-quasi-compact-space)
and Tag 03FX (lemma-cover-by-union-affines)
(blueprint: lem-a1-space-finite-affine-subatlas).

The given disjoint affine summands are expressed as pairwise disjoint affine opens
covering the atlas scheme. Their finite union has its usual restricted scheme structure.
The separate continuous-surjection assertion and its scheme-atlas consequence are included.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

private theorem schemePointMap_comp {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U V : Over S} (k : U ⟶ V)
    (a : yoneda.obj V ⟶ F) (x : U.left) :
    schemePointMap (yoneda.map k ≫ a) x = schemePointMap a (k.left x) := by
  apply Quot.sound
  let e := Spec.map (k.left.residueFieldMap x)
  have he : e ≫ V.left.fromSpecResidueField (k.left x) =
      U.left.fromSpecResidueField x ≫ k.left :=
    k.left.SpecMap_residueFieldMap_fromSpecResidueField x
  let r : Over.mk (U.left.fromSpecResidueField x ≫ U.hom) ⟶
      Over.mk (V.left.fromSpecResidueField (k.left x) ≫ V.hom) :=
    Over.homMk e (by
      change e ≫ (V.left.fromSpecResidueField (k.left x) ≫ V.hom) =
        U.left.fromSpecResidueField x ≫ U.hom
      rw [← Category.assoc, he, Category.assoc, Over.w])
  refine ⟨U.left.residueField x, inferInstance,
    U.left.fromSpecResidueField x ≫ U.hom, 𝟙 _, r, ?_⟩
  dsimp only [PointRepresentative.value]
  rw [CategoryTheory.op_id, F.map_id]
  change (yoneda.map k ≫ a).app _ (Over.homMk _ rfl) =
    F.map r.op (a.app _ (Over.homMk _ rfl))
  rw [← NatTrans.naturality_apply]
  apply congrArg (a.app _)
  apply Over.OverMorphism.ext
  exact he.symm

private theorem schemePointMap_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (a : yoneda.obj T ⟶ F) (ha : IsSurjective a) :
    Function.Surjective (schemePointMap a) := by
  intro x
  induction x using Quot.inductionOn with
  | h x =>
    let t : yoneda.obj (Over.mk x.base) ⟶ F := yonedaEquiv.symm x.value
    obtain ⟨V, p, q, hq, hp⟩ := ha (Over.mk x.base) t
    have : Surjective p.left := hp
    obtain ⟨v, _⟩ := p.left.surjective (IsLocalRing.closedPoint x.K)
    refine ⟨(yoneda.preimage q).left v, ?_⟩
    rw [← schemePointMap_comp, Functor.map_preimage, hq.w]
    apply Quot.sound
    let r : Over.mk (V.left.fromSpecResidueField v ≫ V.hom) ⟶ Over.mk x.base :=
      Over.homMk (V.left.fromSpecResidueField v ≫ p.left) (by
        change (V.left.fromSpecResidueField v ≫ p.left) ≫ (Over.mk x.base).hom =
          V.left.fromSpecResidueField v ≫ V.hom
        rw [Category.assoc, Over.w p])
    refine ⟨V.left.residueField v, inferInstance,
      V.left.fromSpecResidueField v ≫ V.hom, 𝟙 _, r, ?_⟩
    dsimp only [PointRepresentative.value]
    rw [CategoryTheory.op_id, F.map_id]
    change t.app _ ((Over.homMk _ rfl) ≫ p) = F.map r.op x.value
    rw [yonedaEquiv_symm_app_apply]
    rfl

private theorem schemePointMap_continuous {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (a : yoneda.obj T ⟶ F) (ha : IsEtale a) : Continuous (schemePointMap a) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup_of_le T (le_iSup_of_le a (le_iSup_of_le ha le_rfl))

private theorem schemePointMap_open {S : Scheme.{u}} (F : AlgebraicSpace S)
    {T : Over S} (a : yoneda.obj T ⟶ F.obj.obj) (ha : IsEtale a) :
    IsOpenMap (schemePointMap a) := by
  obtain ⟨W, w, I, A, ι, _, _, _, _, _, hw, _, τ, hτ, _, hall⟩ :=
    exists_affine_etale_cover_and_point_topology F
  have heq : pointTopologicalSpace F.obj.obj = τ := by
    apply le_antisymm
    · exact iSup_le fun T ↦ iSup_le fun t ↦ iSup_le fun ht ↦
        (continuous_iff_coinduced_le.mp (hall T t).1)
    · rw [hτ]
      exact continuous_iff_coinduced_le.mp (schemePointMap_continuous w hw)
  change @IsOpenMap _ _ _ (pointTopologicalSpace F.obj.obj) _
  rw [heq]
  exact ((hall T a).2 ha).1

private theorem isEtale_yoneda {S : Scheme.{u}} {U V : Over S}
    (r : U ⟶ V) (hr : Etale r.left) : IsEtale (yoneda.map r) := by
  intro T a
  let b : T ⟶ V := yoneda.preimage a
  refine ⟨Limits.pullback r b, Limits.pullback.snd r b,
    yoneda.map (Limits.pullback.fst r b), ?_, ?_⟩
  · have hb : yoneda.map b = a := yoneda.map_preimage a
    rw [← hb]
    exact (IsPullback.of_hasPullback r b).map yoneda
  · exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback r b).map (Over.forget S)) hr

private theorem schemePointMap_surjective_iff {S : Scheme.{u}} (Z : AlgebraicSpace S)
    {U : Over S} (p : yoneda.obj U ⟶ Z.obj.obj) (hp : IsEtale p) :
    IsSurjective p ↔ Function.Surjective (schemePointMap p) := by
  refine ⟨schemePointMap_surjective p, ?_⟩
  intro hs
  let a : schemeSpace U ⟶ Z := ObjectProperty.homMk ⟨p⟩
  apply (point_open_calculus.2.1 (schemeSpace U) Z a ?_).mpr
  · intro x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨schemePointMap (𝟙 (yoneda.obj U)) y, hy⟩
  · intro T t
    obtain ⟨V, q, r, hr, _⟩ := hp T t
    exact ⟨V, q, r, hr, trivial⟩

/-- A compact point space permits a finite union of the specified affine atlas components.
Source: Stacks Project, Tags 03E4 and 03FX
(blueprint: lem-a1-space-finite-affine-subatlas).

Proof: (1) For any open subscheme of the atlas, a scheme test of its map to `Z` is
an open subscheme of the corresponding scheme test of `p`, by
lem-weil-pbc-open-immersion-base-change. Restricting the etale projection remains etale
by lem-a1-etale-open-restriction, so the restricted map is representable etale.
(2) By lem-a1-space-point-open-calculus, the images of the component restrictions are
open and the atlas point map is surjective. The component cover therefore gives an
open cover of `Point Z.obj.obj` by these images.
(3) Compactness selects a finite subset `D₀` of component indices. The open union `W`
of those components has full point image. Its restricted structure sheaf is precisely
the scheme structure on their disjoint union.
(4) Each affine component is compact by lem-weil-pbc-affine-scheme-qcqs. Restrict an
open cover of `W` to each selected component and combine their finite subcovers, proving
compactness of `W`. If `Z` is empty, select no components and use the empty scheme.
(5) Step (1) makes the restriction representable etale; its full point image makes it
surjective on scheme tests by lem-a1-space-point-open-calculus. -/
theorem exists_finite_affine_subatlas {S : Scheme.{u}} (Z : AlgebraicSpace S)
    (hZ : CompactSpace (Point Z.obj.obj)) (U : Over S)
    (p : yoneda.obj U ⟶ Z.obj.obj) (hp : IsEtale p) (hs : IsSurjective p)
    {D : Type v} (V : D → U.left.Opens) (hV : ∀ d : D, IsAffineOpen (V d))
    (hd : Pairwise (fun d e : D ↦ Disjoint (V d) (V e))) (hc : (⨆ d : D, V d) = ⊤) :
    ∃ (D₀ : Set D) (W : U.left.Opens), D₀.Finite ∧ W = (⨆ d ∈ D₀, V d) ∧
      CompactSpace W.toScheme ∧
      IsEtale (yoneda.map (Over.homMk (U := Over.mk (W.ι ≫ U.hom)) (V := U)
        W.ι rfl) ≫ p) ∧
      IsSurjective (yoneda.map (Over.homMk (U := Over.mk (W.ι ≫ U.hom)) (V := U)
        W.ι rfl) ≫ p) := by
  classical
  have _hdisjoint := hd
  let := hZ
  have hopen := schemePointMap_open Z p hp
  have hsurj := schemePointMap_surjective p hs
  have hcover : (Set.univ : Set (Point Z.obj.obj)) ⊆
      ⋃ d : D, schemePointMap p '' (V d : Set U.left) := by
    intro x _
    obtain ⟨y, rfl⟩ := hsurj x
    have hy : y ∈ (⨆ d : D, V d) := by rw [hc]; trivial
    obtain ⟨d, hd⟩ := (TopologicalSpace.Opens.mem_iSup.mp hy)
    exact Set.mem_iUnion.mpr ⟨d, y, hd, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun d : D ↦ schemePointMap p '' (V d : Set U.left))
    (fun d ↦ hopen _ (V d).isOpen) hcover
  let W : U.left.Opens := ⨆ d ∈ (t : Set D), V d
  let i : Over.mk (W.ι ≫ U.hom) ⟶ U := Over.homMk W.ι rfl
  have he : IsEtale (yoneda.map i ≫ p) :=
    isEtale_comp _ _ (isEtale_yoneda i (show Etale W.ι from inferInstance)) hp
  refine ⟨(t : Set D), W, t.finite_toSet, rfl, ?_, he, ?_⟩
  · change CompactSpace (W : Set U.left)
    apply isCompact_iff_compactSpace.mp
    have hw : IsCompact (⋃ d ∈ (t : Set D), (V d : Set U.left)) :=
      t.finite_toSet.isCompact_biUnion (fun d _ ↦ (hV d).isCompact)
    simpa only [W, TopologicalSpace.Opens.coe_iSup] using hw
  · apply (schemePointMap_surjective_iff Z _ he).mpr
    intro x
    rcases Set.mem_iUnion.mp (ht (Set.mem_univ x)) with ⟨d, hd⟩
    rcases Set.mem_iUnion.mp hd with ⟨hd, y, hy, hyx⟩
    have hyW : y ∈ W := by
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨d,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨hd, hy⟩⟩
    refine ⟨⟨y, hyW⟩, ?_⟩
    rw [schemePointMap_comp]
    exact hyx

/-- A continuous surjective morphism on algebraic-space point classes preserves compactness.
Source: Stacks Project, Tag 03E4, and Topology, Tag 04Z9
(blueprint: lem-a1-space-finite-affine-subatlas).

Proof: step (6) applies lem-weil-pbc-continuous-image-quasi-compact to the stipulated
continuous point map. Its image is compact; surjectivity identifies that image with
the whole target point space. Equivalently, pull an open cover back to the source,
choose a finite subcover there, and use surjectivity to cover the target. This also
handles empty source and target. -/
theorem compactSpace_points_of_surjective {S : Scheme.{u}} (B C : AlgebraicSpace S)
    (f : B ⟶ C) (hf : Continuous (mapPoint f.hom.hom))
    (hs : Function.Surjective (mapPoint f.hom.hom))
    (hB : CompactSpace (Point B.obj.obj)) : CompactSpace (Point C.obj.obj) := by
  let := hB
  exact Function.Surjective.compactSpace hf hs

/-- A quasi-compact scheme atlas has quasi-compact target point space.
Source: Stacks Project, Tag 03E4 (blueprint: lem-a1-space-finite-affine-subatlas).

Proof: in step (6), lem-a1-space-point-open-calculus supplies continuity of the atlas
point map and surjectivity from representable surjectivity. Apply
lem-weil-pbc-continuous-image-quasi-compact to the compact scheme source; its image is
all of the target point space. The argument includes the empty scheme. -/
theorem compactSpace_points_of_scheme_atlas {S : Scheme.{u}} (Z : AlgebraicSpace S)
    (U : Over S) (p : yoneda.obj U ⟶ Z.obj.obj) (hp : IsEtale p)
    (hs : IsSurjective p) (hU : CompactSpace U.left) : CompactSpace (Point Z.obj.obj) := by
  let := hU
  exact Function.Surjective.compactSpace (schemePointMap_continuous p hp)
    (schemePointMap_surjective p hs)

end AlgebraicGeometry.AlgebraicSpace
