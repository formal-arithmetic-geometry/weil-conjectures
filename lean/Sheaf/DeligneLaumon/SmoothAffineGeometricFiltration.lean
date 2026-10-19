/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Topology.StratificationDense
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Smooth affine filtrations over an algebraically closed field

Source: Stacks Project, Tag 0B8X, and the Noetherian induction in
`thm-zl-real-mixed-by-curves`, paragraphs 6--7.
(blueprint: lem-zl-smooth-affine-geometric-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- A reduced closed filtration with one nonempty smooth affine geometric piece per layer.
Source: Stacks Project, Tag 0B8X; blueprint proof paragraphs 6--7
(blueprint: lem-zl-smooth-affine-geometric-filtration). -/
structure SmoothAffineFiltration {S : Scheme.{u}} (X : Over S) (n : ℕ) where
  closed : Fin (n + 1) → Over S
  reduced : ∀ a, IsReduced (closed a).left
  start : closed 0 = X
  finish : IsEmpty (closed (Fin.last n)).left
  inclusion : ∀ a : Fin n, closed a.succ ⟶ closed a.castSucc
  intoAmbient : ∀ a, closed a ⟶ X
  closed_inclusion : ∀ a, IsClosedImmersion (inclusion a).left
  intoAmbient_zero : intoAmbient 0 =
    eqToHom start
  intoAmbient_succ : ∀ a, intoAmbient a.succ = inclusion a ≫ intoAmbient a.castSucc
  piece : Fin n → Over S
  pieceInclusion : ∀ a, piece a ⟶ closed a.castSucc
  open_piece : ∀ a, IsOpenImmersion (pieceInclusion a).left
  range_piece : ∀ a, Set.range (pieceInclusion a).left = (Set.range (inclusion a).left)ᶜ
  nonempty_piece : ∀ a, Nonempty (piece a).left
  reduced_piece : ∀ a, IsReduced (piece a).left
  affine_piece : ∀ a, IsAffine (piece a).left
  connected_piece : ∀ a, GeometricallyConnected (piece a).hom
  dimension : Fin n → ℕ
  smooth_piece : ∀ a, SmoothOfRelativeDimension (dimension a) (piece a).hom

private theorem exists_open_in_partition
    {X : Type u} [TopologicalSpace X] [Nonempty X]
    {A : Type v} [Finite A] (P : A → Set X)
    (hl : ∀ a, IsLocallyClosed (P a)) (hc : (⋃ a, P a) = Set.univ) :
    ∃ (U : TopologicalSpace.Opens X) (a : A), (U : Set X).Nonempty ∧ (U : Set X) ⊆ P a := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, (interior (P a)).Nonempty := by
    by_contra! h
    have hn : IsNowhereDense (⋃ a, P a) := isNowhereDense_iUnion fun a ↦
      (hl a).isNowhereDense_of_interior_eq_empty (h a)
    rw [hc, IsNowhereDense, closure_univ, interior_univ] at hn
    exact Set.univ_nonempty.ne_empty hn
  exact ⟨⟨interior (P a), isOpen_interior⟩, a, ha, interior_subset⟩

private theorem exists_smooth_affine_piece
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y : Over (Spec (.of k))) [IsReduced Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [Nonempty Y.left]
    {A : Type v} [Finite A] (P : A → Set Y.left)
    (hl : ∀ a, IsLocallyClosed (P a)) (hc : (⋃ a, P a) = Set.univ) :
    ∃ (V : Over (Spec (.of k))) (j : V ⟶ Y) (a : A) (d : ℕ),
      IsOpenImmersion j.left ∧ Nonempty V.left ∧ IsReduced V.left ∧
      IsAffine V.left ∧ GeometricallyConnected V.hom ∧
      SmoothOfRelativeDimension d V.hom ∧ Set.range j.left ⊆ P a := by
  classical
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  have : LocallyOfFinitePresentation Y.hom := inferInstance
  obtain ⟨O, a, hOne, hOa⟩ := exists_open_in_partition P hl hc
  let W : Y.left.Opens := O ⊓ Y.hom.smoothLocus
  have hWne : (W : Set Y.left).Nonempty := by
    obtain ⟨x, hxO, hxsm⟩ := Y.hom.dense_smoothLocus_of_perfectField.inter_open_nonempty
      O O.isOpen hOne
    exact ⟨x, hxO, hxsm⟩
  have : Nonempty W.toScheme := hWne.to_subtype
  have : TopologicalSpace.NoetherianSpace W.toScheme :=
    W.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have hWsm : Smooth (W.ι ≫ Y.hom) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    exact x.property.2
  obtain ⟨x⟩ := (inferInstance : Nonempty W.toScheme)
  let C := irreducibleComponent x
  have hC := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨R, hRo, hRne, hRC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  let R' : W.toScheme.Opens := ⟨R, hRo⟩
  have hRirr : IsIrreducible R :=
    hC.1.2.subset_irreducible hRne hRo (fun _ ↦ id) hRC
  have : IrreducibleSpace R'.toScheme := isIrreducible_iff_irreducibleSpace.mp hRirr
  let f := R'.ι ≫ W.ι ≫ Y.hom
  have : Smooth f := inferInstance
  obtain ⟨r⟩ := (inferInstance : Nonempty R'.toScheme)
  obtain ⟨B, V, hB, hV, hr, e, d, hd⟩ :=
    Smooth.exists_smoothOfRelativeDimension_resLE f r
  have : IsAffine V.toScheme := hV
  have : Nonempty V.toScheme := ⟨⟨r, hr⟩⟩
  have : IrreducibleSpace V.toScheme :=
    V.ι.isOpenEmbedding.irreducibleSpace
  let j := V.ι ≫ R'.ι ≫ W.ι
  let V' : Over (Spec (.of k)) := Over.mk (j ≫ Y.hom)
  have hdim : SmoothOfRelativeDimension d (j ≫ Y.hom) := by
    have : SmoothOfRelativeDimension (d + 0) (f.resLE B V e ≫ B.ι) := inferInstance
    simpa [Scheme.Hom.resLE_comp_ι, j, f, Category.assoc] using this
  refine ⟨V', Over.homMk j (by simp [V']), a, d, ?_, ?_, ?_, ?_, ?_, hdim, ?_⟩
  · change IsOpenImmersion (V.ι ≫ R'.ι ≫ W.ι)
    infer_instance
  · exact (inferInstance : Nonempty V.toScheme)
  · exact (inferInstance : IsReduced V.toScheme)
  · exact (inferInstance : IsAffine V.toScheme)
  · change GeometricallyConnected (V.ι ≫ f)
    exact GeometricallyConnected.of_connectedSpace_of_isSepClosed (V.ι ≫ f)
  · rintro _ ⟨z, rfl⟩
    exact hOa (R'.ι (V.ι z)).property.1

private def prependFiltration {S : Scheme.{u}} {Y C : Over S} {n : ℕ}
    [IsReduced Y.left] (i : C ⟶ Y) [IsClosedImmersion i.left]
    (V : Over S) (j : V ⟶ Y) [IsOpenImmersion j.left]
    (hr : Set.range j.left = (Set.range i.left)ᶜ)
    (hne : Nonempty V.left) (hred : IsReduced V.left) (haff : IsAffine V.left)
    (hconn : GeometricallyConnected V.hom) (d : ℕ)
    (hsm : SmoothOfRelativeDimension d V.hom) (H : SmoothAffineFiltration C n) :
    SmoothAffineFiltration Y (n + 1) where
  closed := Fin.cons Y H.closed
  reduced := by
    intro a
    cases a using Fin.cases with
    | zero => exact (inferInstance : IsReduced Y.left)
    | succ a => exact H.reduced a
  start := rfl
  finish := by
    change IsEmpty (H.closed (Fin.last n)).left
    exact H.finish
  inclusion := Fin.cases (eqToHom H.start ≫ i) H.inclusion
  intoAmbient := Fin.cons (𝟙 Y) (fun a ↦ H.intoAmbient a ≫ i)
  closed_inclusion := by
    intro a
    cases a using Fin.cases with
    | zero =>
      change IsClosedImmersion (eqToHom H.start ≫ i).left
      rw [Over.comp_left]
      infer_instance
    | succ a => exact H.closed_inclusion a
  intoAmbient_zero := by rfl
  intoAmbient_succ := by
    intro a
    cases a using Fin.cases with
    | zero =>
      change H.intoAmbient 0 ≫ i = (eqToHom H.start ≫ i) ≫ 𝟙 Y
      rw [H.intoAmbient_zero, Category.comp_id]
    | succ a =>
      change H.intoAmbient a.succ ≫ i = H.inclusion a ≫ H.intoAmbient a.castSucc ≫ i
      rw [H.intoAmbient_succ, Category.assoc]
  piece := Fin.cons V H.piece
  pieceInclusion := Fin.cases j H.pieceInclusion
  open_piece := by
    intro a
    cases a using Fin.cases with
    | zero => exact (inferInstance : IsOpenImmersion j.left)
    | succ a => exact H.open_piece a
  range_piece := by
    intro a
    cases a using Fin.cases with
    | zero =>
      change Set.range j.left = (Set.range (eqToHom H.start ≫ i).left)ᶜ
      rw [Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr (eqToHom H.start).left.surjective, Set.image_univ]
      exact hr
    | succ a => exact H.range_piece a
  nonempty_piece := Fin.cases hne H.nonempty_piece
  reduced_piece := Fin.cases hred H.reduced_piece
  affine_piece := Fin.cases haff H.affine_piece
  connected_piece := Fin.cases hconn H.connected_piece
  dimension := Fin.cons d H.dimension
  smooth_piece := Fin.cases hsm H.smooth_piece

private theorem exists_filtration_on_closed
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    {A : Type v} [Finite A] (P : A → Set X)
    (hl : ∀ a, IsLocallyClosed (P a)) (hc : (⋃ a, P a) = Set.univ)
    (C : TopologicalSpace.Closeds X) :
    ∀ (Y : Over (Spec (.of k))) [IsReduced Y.left]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (z : Y.left ⟶ X) [IsClosedImmersion z], Set.range z = (C : Set X) →
    ∃ (n : ℕ) (H : SmoothAffineFiltration Y n),
      ∀ b : Fin n, ∃ a, Set.range
        (H.pieceInclusion b ≫ H.intoAmbient b.castSucc).left ⊆ z ⁻¹' P a := by
  classical
  induction C using (wellFounded_lt (α := TopologicalSpace.Closeds X)).induction with
  | h C ih =>
    intro Y _ _ _ z _ hz
    by_cases hY : IsEmpty Y.left
    · let H : SmoothAffineFiltration Y 0 := {
        closed := fun _ ↦ Y
        reduced := fun _ ↦ inferInstance
        start := rfl
        finish := hY
        inclusion := fun a ↦ a.elim0
        intoAmbient := fun _ ↦ 𝟙 Y
        closed_inclusion := fun a ↦ a.elim0
        intoAmbient_zero := by rfl
        intoAmbient_succ := fun a ↦ a.elim0
        piece := fun a ↦ a.elim0
        pieceInclusion := fun a ↦ a.elim0
        open_piece := fun a ↦ a.elim0
        range_piece := fun a ↦ a.elim0
        nonempty_piece := fun a ↦ a.elim0
        reduced_piece := fun a ↦ a.elim0
        affine_piece := fun a ↦ a.elim0
        connected_piece := fun a ↦ a.elim0
        dimension := fun a ↦ a.elim0
        smooth_piece := fun a ↦ a.elim0 }
      exact ⟨0, H, fun a ↦ a.elim0⟩
    have : Nonempty Y.left := not_isEmpty_iff.mp hY
    have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
    have : IsNoetherian Y.left := ⟨⟩
    obtain ⟨V, j, a, d, hj, hne, hred, haff, hconn, hsm, hPa⟩ :=
      exists_smooth_affine_piece Y (fun a ↦ z ⁻¹' P a)
        (fun a ↦ (hl a).preimage z.continuous) (by simp [← Set.preimage_iUnion, hc])
    have := hj
    let K : TopologicalSpace.Closeds Y.left :=
      ⟨(Set.range j.left)ᶜ, j.left.isOpenEmbedding.isOpen_range.isClosed_compl⟩
    let I := Scheme.IdealSheafData.vanishingIdeal K
    let Y' : Over (Spec (.of k)) := Over.mk (I.subschemeι ≫ Y.hom)
    let i : Y' ⟶ Y := Over.homMk I.subschemeι (by simp [Y'])
    have hi : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
    have hred' : IsReduced Y'.left := inferInstanceAs (IsReduced I.subscheme)
    have hri : Set.range i.left = (Set.range j.left)ᶜ := by
      change Set.range I.subschemeι = (K : Set Y.left)
      simp [I]
    let C' : TopologicalSpace.Closeds X :=
      ⟨Set.range (i.left ≫ z), (i.left ≫ z).isClosedEmbedding.isClosed_range⟩
    have hlt : C' < C := by
      refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
      · rintro _ ⟨y, rfl⟩
        exact hz.subset ⟨i.left y, rfl⟩
      · intro hle
        obtain ⟨v⟩ := hne
        have hmem : z (j.left v) ∈ (C : Set X) := by rw [← hz]; exact Set.mem_range_self _
        obtain ⟨y, hy⟩ := hle hmem
        have hy' : i.left y = j.left v := z.isClosedEmbedding.injective hy
        have : i.left y ∈ (Set.range j.left)ᶜ := by rw [← hri]; exact Set.mem_range_self _
        exact this (hy' ▸ Set.mem_range_self v)
    have : LocallyOfFiniteType Y'.hom := inferInstanceAs
      (LocallyOfFiniteType (I.subschemeι ≫ Y.hom))
    have : QuasiCompact Y'.hom := inferInstanceAs (QuasiCompact (I.subschemeι ≫ Y.hom))
    obtain ⟨n, H, hH⟩ := ih C' hlt Y' (i.left ≫ z) rfl
    let H' := prependFiltration i V j (by rw [hri, compl_compl])
      hne hred haff hconn d hsm H
    refine ⟨n + 1, H', ?_⟩
    intro b
    cases b using Fin.cases with
    | zero =>
      refine ⟨a, ?_⟩
      change Set.range (j ≫ 𝟙 Y).left ⊆ z ⁻¹' P a
      simpa only [Category.comp_id] using hPa
    | succ b =>
      obtain ⟨a, ha⟩ := hH b
      refine ⟨a, ?_⟩
      rintro _ ⟨v, rfl⟩
      exact ha ⟨v, rfl⟩

/-- Every finite locally closed partition on a reduced finite-type scheme over an
algebraically closed field admits a finite smooth affine closed filtration.
Source: Stacks Project, Tag 0B8X; the Noetherian induction in blueprint
`thm-zl-real-mixed-by-curves`, paragraphs 6--7
(blueprint: lem-zl-smooth-affine-geometric-filtration).

Proof: In a nonempty closed reduced subspace choose an open lying in a single partition
part. Intersect with the dense smooth locus, choose a nonempty open inside an irreducible
component, and shrink to an affine neighbourhood of constant smooth dimension. This
piece is irreducible, hence connected and geometrically connected over the algebraically
closed field. Remove it, give the closed complement its reduced induced structure, and
apply Noetherian induction. Prepend the chosen piece to the resulting finite filtration.
The empty case has length zero. -/
theorem exists_smooth_affine_geometric_filtration
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y : Over (Spec (.of k))) [IsReduced Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    {A : Type v} [Finite A] (P : A → Set Y.left)
    (hl : ∀ a, IsLocallyClosed (P a)) (hc : (⋃ a, P a) = Set.univ) :
    ∃ (n : ℕ) (H : SmoothAffineFiltration Y n),
      ∀ b : Fin n, ∃ a, Set.range
        (H.pieceInclusion b ≫ H.intoAmbient b.castSucc).left ⊆ P a := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  simpa using exists_filtration_on_closed Y.left P hl hc ⊤ Y (𝟙 Y.left) (by simp)

end WeilConjectures
