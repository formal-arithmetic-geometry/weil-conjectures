/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Compatibilities of the comparison isomorphisms for functors preserving homology

For a functor `F` preserving the left homology of a short complex `S`, the comparison
isomorphisms `(S.map F).cycles ≅ F.obj S.cycles` and `(S.map F).homology ≅ F.obj S.homology`
are compatible with `toCycles` and `homologyπ`.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Category Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

@[reassoc (attr := simp)]
lemma toCycles_mapCyclesIso_hom [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).toCycles ≫ (S.mapCyclesIso F).hom = F.map S.toCycles := by
  have : Mono (F.map S.iCycles) := by
    rw [← mapCyclesIso_hom_iCycles]
    infer_instance
  rw [← cancel_mono (F.map S.iCycles), assoc, mapCyclesIso_hom_iCycles, toCycles_i,
    ← F.map_comp, toCycles_i]
  rfl

@[reassoc]
lemma homologyπ_mapHomologyIso_hom [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let hl := S.leftHomologyData
  have h₁ := hl.homologyπ_comp_homologyIso_hom
  have h₂ := (hl.map F).homologyπ_comp_homologyIso_hom
  rw [LeftHomologyData.mapHomologyIso_eq hl, LeftHomologyData.mapCyclesIso_eq hl]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, assoc]
  rw [reassoc_of% h₂, LeftHomologyData.map_π, ← F.map_comp, ← F.map_comp]
  congr 2
  rw [← cancel_epi hl.cyclesIso.hom, Iso.hom_inv_id_assoc, ← reassoc_of% h₁, Iso.hom_inv_id,
    comp_id]

end CategoryTheory.ShortComplex
