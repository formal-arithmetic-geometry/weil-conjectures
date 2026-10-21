/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-! # The change of indices in the Künneth spectral sequence

Source: Stacks Project, Tag 0H7Z.
(blueprint: lem-kun-spectral-sequence-reindex).
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The integer lattice change in Stacks Tag 0H7Z. -/
def kunnethIndex (pq : ℤ × ℤ) : ℤ × ℤ := (-pq.2, pq.1 + 2 * pq.2)

/-- The new r-page shape embeds into the old (r-1)-page shape. -/
def kunnethShapeEmbedding (r : ℤ) :
    (ComplexShape.up' (r, 1 - r)).Embedding (ComplexShape.up' (r - 1, 1 - (r - 1))) :=
  ComplexShape.Embedding.mk' _ _ kunnethIndex (by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [kunnethIndex, Prod.mk.injEq] at h
    congr 1 <;> omega) (by
    rintro ⟨p, q⟩ ⟨p', q'⟩
    change (p + r, q + (1 - r)) = (p', q') ↔
      (-q + (r - 1), p + 2 * q + (1 - (r - 1))) = (-q', p' + 2 * q')
    simp only [Prod.mk.injEq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> omega)

/-- The index map preserves and reflects the differential relation. -/
instance (r : ℤ) : (kunnethShapeEmbedding r).IsRelIff := by
  unfold kunnethShapeEmbedding
  infer_instance

variable {C : Type*} [Category C] [Abelian C]

/-- Predecessor for the cohomological spectral-sequence shape. -/
theorem kunneth_prev (r : ℤ) (pq : ℤ × ℤ) :
    (ComplexShape.up' (r, 1 - r)).prev pq = pq - (r, 1 - r) := by
  apply ComplexShape.prev_eq'
  change pq - (r, 1 - r) + (r, 1 - r) = pq
  exact sub_add_cancel _ _

/-- Successor for the cohomological spectral-sequence shape. -/
theorem kunneth_next (r : ℤ) (pq : ℤ × ℤ) :
    (ComplexShape.up' (r, 1 - r)).next pq = pq + (r, 1 - r) := by
  apply ComplexShape.next_eq'
  rfl

/-- Restricting along the lattice change preserves homology at each index. -/
def reindexHomologyIso (r : ℤ)
    (K : HomologicalComplex C (ComplexShape.up' (r - 1, 1 - (r - 1)))) (pq : ℤ × ℤ) :
    (K.restriction (kunnethShapeEmbedding r)).homology pq ≅ K.homology (kunnethIndex pq) :=
  K.restrictionHomologyIso (kunnethShapeEmbedding r)
    (pq - (r, 1 - r)) pq (pq + (r, 1 - r))
    (kunneth_prev r pq) (kunneth_next r pq) rfl rfl rfl (by
      apply ComplexShape.prev_eq'
      change kunnethIndex (pq - (r, 1 - r)) + (r - 1, 1 - (r - 1)) = kunnethIndex pq
      ext <;> dsimp [kunnethIndex] <;> omega) (by
      apply ComplexShape.next_eq'
      change kunnethIndex pq + (r - 1, 1 - (r - 1)) = kunnethIndex (pq + (r, 1 - r))
      ext <;> dsimp [kunnethIndex] <;> omega)

/-- Restricting along the lattice change preserves cycles at each index. -/
def reindexCyclesIso (r : ℤ)
    (K : HomologicalComplex C (ComplexShape.up' (r - 1, 1 - (r - 1))))
    (pq : ℤ × ℤ) :
    (K.restriction (kunnethShapeEmbedding r)).cycles pq ≅ K.cycles (kunnethIndex pq) :=
  K.restrictionCyclesIso (kunnethShapeEmbedding r)
    pq (pq + (r, 1 - r)) (kunneth_next r pq) rfl rfl (by
      apply ComplexShape.next_eq'
      change kunnethIndex pq + (r - 1, 1 - (r - 1)) =
        kunnethIndex (pq + (r, 1 - r))
      ext <;> dsimp [kunnethIndex] <;> omega)

@[reassoc]
private theorem reindex_homologyπ (r : ℤ)
    (K : HomologicalComplex C (ComplexShape.up' (r - 1, 1 - (r - 1))))
    (pq : ℤ × ℤ) :
    (K.restriction (kunnethShapeEmbedding r)).homologyπ pq ≫
        (reindexHomologyIso r K pq).hom =
      (reindexCyclesIso r K pq).hom ≫ K.homologyπ (kunnethIndex pq) := by
  exact K.homologyπ_restrictionHomologyIso_hom _ _ _ _ _ _ _ _ _ _ _

@[reassoc]
private theorem reindex_cycles_i (r : ℤ)
    (K : HomologicalComplex C (ComplexShape.up' (r - 1, 1 - (r - 1))))
    (pq : ℤ × ℤ) :
    (reindexCyclesIso r K pq).hom ≫ K.iCycles (kunnethIndex pq) =
      (K.restriction (kunnethShapeEmbedding r)).iCycles pq := by
  simpa only [reindexCyclesIso, kunnethShapeEmbedding, ComplexShape.Embedding.mk',
    HomologicalComplex.restrictionXIso, eqToIso_refl, Iso.refl_hom,
    Category.comp_id] using
    K.restrictionCyclesIso_hom_iCycles (kunnethShapeEmbedding r)
      pq (pq + (r, 1 - r)) (kunneth_next r pq) rfl rfl (by
        apply ComplexShape.next_eq'
        change kunnethIndex pq + (r - 1, 1 - (r - 1)) =
          kunnethIndex (pq + (r, 1 - r))
        ext <;> dsimp [kunnethIndex] <;> omega)

private theorem reindexHomologyIso_naturality (r : ℤ)
    {K L : HomologicalComplex C (ComplexShape.up' (r - 1, 1 - (r - 1)))}
    (f : K ⟶ L) (pq : ℤ × ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f
        (kunnethShapeEmbedding r)) pq ≫ (reindexHomologyIso r L pq).hom =
      (reindexHomologyIso r K pq).hom ≫
        HomologicalComplex.homologyMap f (kunnethIndex pq) := by
  have hc : HomologicalComplex.cyclesMap
        (HomologicalComplex.restrictionMap f (kunnethShapeEmbedding r)) pq ≫
        (reindexCyclesIso r L pq).hom =
      (reindexCyclesIso r K pq).hom ≫
        HomologicalComplex.cyclesMap f (kunnethIndex pq) := by
    apply (cancel_mono (L.iCycles (kunnethIndex pq))).1
    simp only [Category.assoc, reindex_cycles_i, HomologicalComplex.cyclesMap_i,
      reindex_cycles_i_assoc, HomologicalComplex.restrictionMap_f]
    rfl
  apply (cancel_epi ((K.restriction (kunnethShapeEmbedding r)).homologyπ pq)).1
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    reindex_homologyπ, reindex_homologyπ_assoc, ← Category.assoc, hc,
    Category.assoc, ← HomologicalComplex.homologyπ_naturality]

/-- The Künneth change of indices, including the successor-page homology maps.
Source: Stacks Project, Tag 0H7Z (blueprint: lem-kun-spectral-sequence-reindex). -/
def kunnethReindex (E : CohomologicalSpectralSequence C 1) :
    E₂CohomologicalSpectralSequence C where
  page r hr := (E.page (r - 1) (by omega)).restriction (kunnethShapeEmbedding r)
  iso r r' pq hrr' hr := reindexHomologyIso r (E.page (r - 1) (by omega)) pq ≪≫
    E.iso (r - 1) (r' - 1) (kunnethIndex pq) (by omega) (by omega)

/-- Reindexing is functorial on all pages.
Source: Stacks Project, Tag 0H7Z (blueprint: lem-kun-spectral-sequence-reindex). -/
def kunnethReindexFunctor :
    CohomologicalSpectralSequence C 1 ⥤ E₂CohomologicalSpectralSequence C where
  obj E := kunnethReindex E
  map f := {
    hom r hr := HomologicalComplex.restrictionMap (f.hom (r - 1) (by omega))
      (kunnethShapeEmbedding r)
    comm r r' pq hrr' hr := by
      dsimp only [kunnethReindex, Iso.trans_hom]
      rw [← Category.assoc, reindexHomologyIso_naturality, Category.assoc,
        f.comm (r - 1) (r' - 1) (kunnethIndex pq) (by omega) (by omega)]
      simp only [Category.assoc, HomologicalComplex.restrictionMap_f]
      rfl }
  map_id E := by ext r hr pq; rfl
  map_comp f g := by ext r hr pq; rfl

/-- Reindexing preserves the normalized stationary successor equation.
Source: Stacks Project, Tag 0H7Z (blueprint: lem-kun-spectral-sequence-reindex).
Proof. Apply the old equation after the canonical isomorphism of cycle objects.
The restriction-homology comparison commutes with the homology projection. -/
theorem kunnethReindex_successor (E : CohomologicalSpectralSequence C 1)
    (pq : ℤ × ℤ) (r : ℤ) (hr : 2 ≤ r) (A : C)
    (e : A ≅ (E.page (r - 1) (by omega)).X (kunnethIndex pq))
    (e' : A ≅ (E.page ((r + 1) - 1) (by omega)).X (kunnethIndex pq))
    (h : (E.page (r - 1) (by omega)).iCycles (kunnethIndex pq) ≫ e.inv =
      (E.page (r - 1) (by omega)).homologyπ (kunnethIndex pq) ≫
        (E.iso (r - 1) ((r + 1) - 1) (kunnethIndex pq) (by omega) (by omega)).hom ≫
          e'.inv) :
    ((kunnethReindex E).page r hr).iCycles pq ≫ e.inv =
      ((kunnethReindex E).page r hr).homologyπ pq ≫
        ((kunnethReindex E).iso r (r + 1) pq rfl hr).hom ≫ e'.inv := by
  dsimp only [kunnethReindex, Iso.trans_hom]
  rw [← reindex_cycles_i r (E.page (r - 1) (by omega)) pq,
    Category.assoc, h, ← reindex_homologyπ_assoc]
  simp only [Category.assoc]

/-- Incoming and outgoing differentials vanish after the change of indices whenever
both old differentials vanish.
Source: Stacks Project, Tag 0H7Z (blueprint: lem-kun-spectral-sequence-reindex).
Proof. The index embedding takes the predecessor and successor to the old predecessor
and successor, respectively. Both equations therefore are the old zero equations. -/
theorem kunnethReindex_differentials (E : CohomologicalSpectralSequence C 1)
    (pq : ℤ × ℤ) (r : ℤ) (hr : 2 ≤ r)
    (h : (E.page (r - 1) (by omega)).dFrom (kunnethIndex pq) = 0 ∧
      (E.page (r - 1) (by omega)).dTo (kunnethIndex pq) = 0) :
    ((kunnethReindex E).page r hr).dFrom pq = 0 ∧
      ((kunnethReindex E).page r hr).dTo pq = 0 := by
  have hn : kunnethIndex ((ComplexShape.up' (r, 1 - r)).next pq) =
      (ComplexShape.up' (r - 1, 1 - (r - 1))).next (kunnethIndex pq) := by
    rw [kunneth_next, kunneth_next]
    ext <;> dsimp [kunnethIndex] <;> omega
  have hp : kunnethIndex ((ComplexShape.up' (r, 1 - r)).prev pq) =
      (ComplexShape.up' (r - 1, 1 - (r - 1))).prev (kunnethIndex pq) := by
    rw [kunneth_prev, kunneth_prev]
    ext <;> dsimp [kunnethIndex] <;> omega
  constructor
  · change (E.page (r - 1) (by omega)).d (kunnethIndex pq)
      (kunnethIndex ((ComplexShape.up' (r, 1 - r)).next pq)) = 0
    rw [hn]
    exact h.1
  · change (E.page (r - 1) (by omega)).d
      (kunnethIndex ((ComplexShape.up' (r, 1 - r)).prev pq)) (kunnethIndex pq) = 0
    rw [hp]
    exact h.2

end CategoryTheory
