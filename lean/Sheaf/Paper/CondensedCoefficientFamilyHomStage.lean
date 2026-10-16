/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Sheaf.Paper.CondensedCoefficientHomStage

/-!
# A common finite coefficient stage for a finite family of homomorphisms

Source: archived `TwoColimit.lean`, the common-stage step in overlap Hom descent.
(blueprint: lem-weil-pbc-condensed-coefficient-family-hom-stage).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- A finite family of finitely presented source modules admits one common Hom stage.

Source: archived `TwoColimit.lean`, common finite-stage Hom descent on the overlaps.
(blueprint: lem-weil-pbc-condensed-coefficient-family-hom-stage).

Proof: apply `condensed_coefficient_hom_stage` separately on each qcqs scheme.
Filteredness supplies a common upper field for E and the finitely many resulting
fields. Including E handles the empty family as well. Compose each descended map
with the specified scalar-inclusion map to this upper field. The composition theorem
for mixed scalar maps and the coefficient-inclusion composition equation verify all
factorizations. No finite-presentation assumption on the target modules is used.
-/
theorem condensed_coefficient_family_hom_stage
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (J : Type u) [Finite J] (Y : J → Scheme.{u})
    [∀ j, CompactSpace (Y j)] [∀ j, QuasiSeparatedSpace (Y j)]
    (P Q : ∀ j, Mod (Sheaf (Scheme.ProEt.topology (Y j)) Ab.{u + 1})
      (padicSubfieldRingObj (Y j) ℓ E))
    (hP : ∀ j, Mod.IsFinitelyPresented (padicSubfieldRingObj (Y j) ℓ E) (P j))
    (a : ∀ j, P j ⟶ (Mod.comap (padicSubfieldRingObjToPadicAlgCl (Y j) ℓ E)).obj
      ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl (Y j) ℓ E)).obj (Q j))) :
    ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (hEF : E ≤ F)
      (b : ∀ j, P j ⟶ (Mod.comap (padicSubfieldRingObjMap (Y j) ℓ hEF)).obj
        ((Mod.extendScalars (padicSubfieldRingObjMap (Y j) ℓ hEF)).obj (Q j))),
      ∀ j, b j ≫ Mod.mixedScalarMap
        (padicSubfieldRingObjMap (Y j) ℓ hEF) (padicSubfieldRingObjToPadicAlgCl (Y j) ℓ E)
        (padicSubfieldRingObjMap (Y j) ℓ hEF) (padicSubfieldRingObjToPadicAlgCl (Y j) ℓ E)
        (padicSubfieldRingObjToPadicAlgCl (Y j) ℓ F)
        (padicSubfieldRingObjMap_comp_toPadicAlgCl (Y j) ℓ hEF)
        (padicSubfieldRingObjMap_comp_toPadicAlgCl (Y j) ℓ hEF) (Q j) = a j := by
  classical
  choose F hEF b hb using fun j ↦ condensed_coefficient_hom_stage
    (Y j) ℓ E (P j) (Q j) (hP j) (a j)
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨G, hG⟩ := IsFiltered.sup_objs_exists (insert E (Finset.univ.image F))
  let hEG : E ≤ G := leOfHom (Classical.choice (hG (Finset.mem_insert_self _ _)))
  let hFG (j : J) : F j ≤ G := leOfHom (Classical.choice
    (hG (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))))
  let c (j : J) := Mod.mixedScalarMap
    (padicSubfieldRingObjMap (Y j) ℓ (hEF j)) (padicSubfieldRingObjMap (Y j) ℓ hEG)
    (padicSubfieldRingObjMap (Y j) ℓ (hEF j)) (padicSubfieldRingObjMap (Y j) ℓ hEG)
    (padicSubfieldRingObjMap (Y j) ℓ (hFG j))
    (coefficientComplex_ringMap_comp (Y j) ℓ (hEF j) (hFG j))
    (coefficientComplex_ringMap_comp (Y j) ℓ (hEF j) (hFG j)) (Q j)
  refine ⟨G, hEG, fun j ↦ b j ≫ c j, ?_⟩
  intro j
  have hc := Mod.mixedScalarMap_comp
    (padicSubfieldRingObjMap (Y j) ℓ (hEF j)) (padicSubfieldRingObjMap (Y j) ℓ hEG)
    (padicSubfieldRingObjToPadicAlgCl (Y j) ℓ E)
    (padicSubfieldRingObjMap (Y j) ℓ (hEF j)) (padicSubfieldRingObjMap (Y j) ℓ hEG)
    (padicSubfieldRingObjToPadicAlgCl (Y j) ℓ E)
    (padicSubfieldRingObjMap (Y j) ℓ (hFG j)) (padicSubfieldRingObjToPadicAlgCl (Y j) ℓ G)
    (coefficientComplex_ringMap_comp (Y j) ℓ (hEF j) (hFG j))
    (padicSubfieldRingObjMap_comp_toPadicAlgCl (Y j) ℓ hEG)
    (coefficientComplex_ringMap_comp (Y j) ℓ (hEF j) (hFG j))
    (padicSubfieldRingObjMap_comp_toPadicAlgCl (Y j) ℓ hEG) (Q j)
  simp only [padicSubfieldRingObjMap_comp_toPadicAlgCl (Y j) ℓ (hFG j)] at hc
  dsimp only [c]
  rw [Category.assoc, ← hc]
  exact hb j

end AlgebraicGeometry.ProEtale
