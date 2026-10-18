/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite
import Sheaf.AlgebraicGeometry.EtaleGeometricFiberClopenPartition
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Mathlib.Algebra.Algebra.Defs
import Sheaf.AlgebraicGeometry.GeometricComponentCountBaseChange

/-!
# Lower semicontinuity of geometric connected component counts

Source: Stacks Project, More on Morphisms, Tag 0BUI,
`lemma-proper-flat-nr-geom-conn-comps-lower-semicontinuous`
(blueprint: lem-weil-pbc-flat-proper-component-count-lower-semicontinuous).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private noncomputable abbrev closurePoint (S : Scheme.{u}) (s : S) :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
    (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s

private noncomputable abbrev geomFiber {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :=
  (pullback f (closurePoint S s) : Scheme.{u})

private theorem finite_geomFiber_components {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] (s : S) : Finite (ConnectedComponents (geomFiber f s)) := by
  have : IsLocallyNoetherian (geomFiber f s) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (closurePoint S s))
  have : CompactSpace (geomFiber f s) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (closurePoint S s))
  have : IsNoetherian (geomFiber f s) := {}
  infer_instance

private theorem geomFiber_count_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] {U : Scheme.{u}} (g : U ⟶ S) (u : U) :
    Nat.card (ConnectedComponents (geomFiber (pullback.snd f g) u)) =
      Nat.card (ConnectedComponents (geomFiber f (g u))) := by
  have := finite_geomFiber_components f (g u)
  have := finite_geomFiber_components (pullback.snd f g) u
  have h := (geometricComponentCount_baseChange f).2 U g u
    (AlgebraicClosure (S.residueField (g u))) (AlgebraicClosure (U.residueField u))
    (CommRingCat.ofHom (algebraMap (S.residueField (g u))
      (AlgebraicClosure (S.residueField (g u)))))
    (CommRingCat.ofHom (algebraMap (U.residueField u)
      (AlgebraicClosure (U.residueField u))))
  simpa only [ENat.card_eq_coe_natCard, ENat.natCast_inj] using h

private theorem geomFiber_projection_apply {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (x : geomFiber f s) :
    f (pullback.fst f (closurePoint S s) x) = s := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  change S.fromSpecResidueField s _ = s
  exact S.fromSpecResidueField_apply s _

private theorem range_geomFiber_projection {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    Set.range (pullback.fst f (closurePoint S s)) = f ⁻¹' {s} := by
  rw [Scheme.Pullback.range_fst]
  have hrange : Set.range (closurePoint S s) = {s} := by
    have hconst (y : Spec (.of (AlgebraicClosure (S.residueField s)))) :
        closurePoint S s y = s := by
      change S.fromSpecResidueField s _ = s
      exact S.fromSpecResidueField_apply s _
    ext t
    simp only [Set.mem_range, Set.mem_singleton_iff, hconst, exists_const, eq_comm]
  rw [hrange]

private theorem card_le_components_of_disjoint_clopens
    {Y : Type*} [TopologicalSpace Y] [Finite (ConnectedComponents Y)]
    {m : ℕ} (V : Fin m → Set Y) (hc : ∀ i, IsClopen (V i))
    (hd : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (hn : ∀ i, (V i).Nonempty) : m ≤ Nat.card (ConnectedComponents Y) := by
  classical
  choose y hy using hn
  have hinj : Function.Injective (fun i ↦ ConnectedComponents.mk (y i)) := by
    intro i j hij
    apply hd.eq
    rw [Set.not_disjoint_iff]
    refine ⟨y i, hy i, ?_⟩
    have heq := ConnectedComponents.coe_eq_coe.mp hij
    exact (hc j).connectedComponent_subset (hy j) (heq ▸ mem_connectedComponent)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ hinj

/-- Source: Stacks Project, More on Morphisms, Tag 0BUI.
(blueprint: lem-weil-pbc-flat-proper-component-count-lower-semicontinuous)

The geometric fibres of a proper flat finitely presented morphism have finitely many
connected components. Their count is zero for an empty fibre and is lower semicontinuous,
expressed by the neighbourhood inequality. The function `n` is specified by `Nat.card` of
`ConnectedComponents`, the quotient by equality of maximal connected subsets.
Properness already implies quasi-compactness and quasi-separatedness, so finite
presentation is expressed by the remaining locally-of-finite-presentation condition.

Proof:
1. Restrict to an affine neighbourhood of a chosen point. Proper base change and flatness
   preserve the hypotheses. Apply affine Stein factorization
   (`lem-weil-pbc-stein-factorization-affine`) and its finite-fibre/residue-field lemma
   (`lem-weil-pbc-stein-finite-fibres-residue-fields`).
2. Apply `lem-weil-pbc-integral-fibre-etale-splitting`: after an affine etale neighbourhood
   the integral intermediate scheme splits into finitely many clopen pieces, each having
   one point over the chosen point, with purely inseparable residue extension. Pull these
   pieces back to a finite clopen partition of the source.
3. By `lem-weil-pbc-geometric-component-count-base-change` counts are unchanged at points
   of this neighbourhood. Flat base change and finite-presentation permanence give flat,
   locally finitely presented restrictions to each piece.
4. A purely inseparable residue extension gives a radicial fibre. Over an algebraic closure
   it has exactly one point: at most one by universal injectivity, and at least one by the
   unique-root embedding of a purely inseparable extension into that closure. Geometric
   connectedness of the Stein fibres makes each source piece nonempty and connected there.
5. These clopen connected nonempty pieces are exactly the connected components. Their
   finite number is the count at the chosen point. This works at every point, including
   the empty partition, whose count is zero.
6. By `lem-weil-pbc-flat-lfp-open`, each source piece has open image containing the chosen
   point. Intersect these finitely many images. Every geometric fibre over the intersection
   meets each piece: extension to the algebraic closure is faithfully flat and surjective
   on spectra (`lem-weil-pbc-field-extension-base-change-faithfully-flat` and
   `lem-weil-pbc-faithfully-flat-surjective-spectrum`). Thus its count is at least the
   number of pieces. For zero pieces the inequality holds on the whole base.
7. The etale map is open (`lem-weil-pbc-etale-morphism-open-map`), so the image of this
   intersection is the desired open neighbourhood on the original base. Base-change
   invariance transfers the inequality. These neighbourhoods also make every strict
   superlevel set open, the equivalent lower-semicontinuity formulation.
-/
theorem Scheme.Hom.geometricComponentCount_lowerSemicontinuous
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] :
    ∃ n : S → ℕ,
      (∀ s : S,
        Finite (ConnectedComponents (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
            (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u})) ∧
        n s = Nat.card (ConnectedComponents (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
            (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u}))) ∧
      (∀ s : S, IsEmpty (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
          (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u}) →
        n s = 0) ∧
      ∀ s : S, ∃ V : S.Opens, s ∈ V ∧ ∀ t : S, t ∈ V → n s ≤ n t := by
  refine ⟨fun s ↦ Nat.card (ConnectedComponents (geomFiber f s)), ?_, ?_, ?_⟩
  · intro s
    exact ⟨finite_geomFiber_components f s, rfl⟩
  · intro s hs
    have : IsEmpty (ConnectedComponents (geomFiber f s)) :=
      ConnectedComponents.isEmpty_iff_isEmpty.mpr hs
    exact Nat.card_of_isEmpty
  intro s
  obtain ⟨U, g, u, hg, hgu, m, V, hVc, hVd, hVcover, hVconn⟩ :=
    f.exists_etale_geometricFiber_clopen_partition s
  have : Etale g := hg
  let p := pullback.snd f g
  let C (w : U) (i : Fin m) : Set (geomFiber p w) :=
    pullback.fst p (closurePoint U w) ⁻¹' (V i : Set ↥(pullback f g))
  have hCc (w : U) (i : Fin m) : IsClopen (C w i) :=
    (show IsClopen (V i : Set ↥(pullback f g)) from ⟨hVc i, (V i).isOpen⟩).preimage
      (pullback.fst p (closurePoint U w)).continuous
  have hCd (w : U) : Pairwise (fun i j ↦ Disjoint (C w i) (C w j)) := by
    intro i j hij
    exact ((TopologicalSpace.Opens.coe_disjoint).mpr (hVd hij)).preimage _
  have hCcover (w : U) : ⋃ i, C w i = Set.univ := by
    change (⋃ i, pullback.fst p (closurePoint U w) ⁻¹'
      (V i : Set ↥(pullback f g))) = Set.univ
    rw [← Set.preimage_iUnion]
    have hv : ⋃ i, (V i : Set ↥(pullback f g)) = Set.univ := by
      rw [← TopologicalSpace.Opens.coe_iSup, hVcover]
      rfl
    rw [hv, Set.preimage_univ]
  have hcount : Nat.card (ConnectedComponents (geomFiber f s)) = m := by
    rw [← hgu, ← geomFiber_count_baseChange f g u]
    simpa only [Nat.card_fin] using Nat.card_congr
      (ConnectedComponents.equivOfIsClopenOfIsConnected (hCc u) (hCd u) (hCcover u)
        hVconn)
  let W : Set U := ⋂ i, p '' (V i : Set ↥(pullback f g))
  have hWo : IsOpen W := isOpen_iInter_of_finite fun i ↦ p.isOpenMap _ (V i).isOpen
  have huW : u ∈ W := by
    refine Set.mem_iInter.mpr fun i ↦ ?_
    obtain ⟨z, hz⟩ := (hVconn i).nonempty
    exact ⟨pullback.fst p (closurePoint U u) z, hz, geomFiber_projection_apply p u z⟩
  refine ⟨⟨g '' W, g.isOpenMap _ hWo⟩, ⟨u, huW, hgu⟩, ?_⟩
  rintro t ⟨w, hw, rfl⟩
  change Nat.card (ConnectedComponents (geomFiber f s)) ≤
    Nat.card (ConnectedComponents (geomFiber f (g w)))
  rw [hcount, ← geomFiber_count_baseChange f g w]
  have := finite_geomFiber_components p w
  apply card_le_components_of_disjoint_clopens (C w) (hCc w) (hCd w)
  intro i
  obtain ⟨x, hxi, hxw⟩ := Set.mem_iInter.mp hw i
  have hx : x ∈ Set.range (pullback.fst p (closurePoint U w)) := by
    rw [range_geomFiber_projection]
    exact hxw
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, show pullback.fst p (closurePoint U w) z ∈ V i from hz.symm ▸ hxi⟩

end AlgebraicGeometry
