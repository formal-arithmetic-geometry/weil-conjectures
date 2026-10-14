/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.SingleHomology

/-! # The reverse homology comparison for a left exact functor

Source: Stacks Project, Tag 0AVW, canonical cohomology comparison on a resolution. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace CategoryTheory.ShortComplex
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The cycles of the mapped complex map to the image of the original cycles by
preservation of the kernel. This uses no exactness of cokernels. -/
def leftExactCyclesComparison (S : ShortComplex C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] :
    (S.map F).cycles ⟶ F.obj S.cycles := by
  let h := KernelFork.mapIsLimit _ S.cyclesIsKernel F
  exact h.lift (KernelFork.ofι (S.map F).iCycles (S.map F).iCycles_g)

@[reassoc (attr := simp)]
theorem leftExactCyclesComparison_i (S : ShortComplex C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] :
    leftExactCyclesComparison S F ≫ F.map S.iCycles = (S.map F).iCycles := by
  exact Fork.IsLimit.lift_ι _

/-- The reverse homology comparison is the cokernel descent of the mapped
cycle-class projection. Inverting this map on an affine K-injective representative
constructs the affine edge; no normalization equation for exact families is used. -/
def leftExactHomologyComparison (S : ShortComplex C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] :
    (S.map F).homology ⟶ F.obj S.homology := by
  refine (S.map F).descHomology
    (leftExactCyclesComparison S F ≫ F.map S.homologyπ) ?_
  have h : (S.map F).toCycles ≫ leftExactCyclesComparison S F = F.map S.toCycles := by
    apply (cancel_mono (F.map S.iCycles)).1
    simp only [Category.assoc, leftExactCyclesComparison_i,
      toCycles_i, ← F.map_comp]
    rfl
  rw [← Category.assoc, h, ← F.map_comp, toCycles_comp_homologyπ, F.map_zero]

@[reassoc (attr := simp)]
theorem leftExactHomologyComparison_π (S : ShortComplex C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] :
    (S.map F).homologyπ ≫ leftExactHomologyComparison S F =
      leftExactCyclesComparison S F ≫ F.map S.homologyπ := by
  exact (S.map F).π_descHomology _ _

variable {E : Type u₃} [Category.{v₃} E] [Abelian E]

/-- Kernel lifts commute with an exact first functor. -/
theorem leftExactCyclesComparison_map (S : ShortComplex C) (F : C ⥤ D) (P : D ⥤ E)
    [F.Additive] [P.Additive]
    [F.PreservesZeroMorphisms] [F.PreservesHomology]
    [P.PreservesZeroMorphisms] [PreservesFiniteLimits P]
    [(F ⋙ P).PreservesHomology] :
    leftExactCyclesComparison (S.map F) P ≫ P.map (S.mapCyclesIso F).hom =
      (S.mapCyclesIso (F ⋙ P)).hom := by
  let : PreservesFiniteLimits (F ⋙ P) :=
    Functor.preservesFiniteLimits_of_preservesHomology (F ⋙ P)
  apply (cancel_mono ((F ⋙ P).map S.iCycles)).1
  simp only [Functor.comp_map, Category.assoc, ← P.map_comp,
    mapCyclesIso_hom_iCycles, leftExactCyclesComparison_i]
  exact (mapCyclesIso_hom_iCycles S (F ⋙ P)).symm

/-- The reverse comparison agrees with exact-homology comparisons whenever both
F and its composite with the left exact functor P preserve homology. -/
theorem leftExactHomologyComparison_map (S : ShortComplex C) (F : C ⥤ D) (P : D ⥤ E)
    [F.Additive] [P.Additive]
    [F.PreservesZeroMorphisms] [F.PreservesHomology]
    [P.PreservesZeroMorphisms] [PreservesFiniteLimits P]
    [(F ⋙ P).PreservesHomology] :
    (S.mapHomologyIso (F ⋙ P)).inv ≫ leftExactHomologyComparison (S.map F) P =
      P.map (S.mapHomologyIso F).inv := by
  have h : leftExactHomologyComparison (S.map F) P ≫ P.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ P)).hom := by
    apply (cancel_epi ((S.map F).map P).homologyπ).1
    simp only [leftExactHomologyComparison_π_assoc, ← P.map_comp,
      homologyπ_mapHomologyIso_hom]
    rw [P.map_comp]
    rw [← Category.assoc, leftExactCyclesComparison_map]
    exact homologyπ_mapHomologyIso_hom (F ⋙ P) S |>.symm
  apply (cancel_mono (P.map (S.mapHomologyIso F).hom)).1
  rw [Category.assoc, h, Iso.inv_hom_id, ← P.map_comp, Iso.inv_hom_id, P.map_id]
  rfl

/-- Naturality of the preserved-kernel lift. -/
@[reassoc]
theorem leftExactCyclesComparison_naturality {S₁ S₂ : ShortComplex C}
    (f : S₁ ⟶ S₂) (P : C ⥤ D)
    [P.PreservesZeroMorphisms] [PreservesFiniteLimits P] :
    cyclesMap (P.mapShortComplex.map f) ≫ leftExactCyclesComparison S₂ P =
      leftExactCyclesComparison S₁ P ≫ P.map (cyclesMap f) := by
  apply (cancel_mono (P.map S₂.iCycles)).1
  simp only [Category.assoc, leftExactCyclesComparison_i, ← P.map_comp, cyclesMap_i]
  erw [P.map_comp, ← Category.assoc, leftExactCyclesComparison_i, cyclesMap_i]
  rfl

/-- Naturality of the reverse homology comparison, proved by cokernel cancellation. -/
@[reassoc]
theorem leftExactHomologyComparison_naturality {S₁ S₂ : ShortComplex C}
    (f : S₁ ⟶ S₂) (P : C ⥤ D)
    [P.PreservesZeroMorphisms] [PreservesFiniteLimits P] :
    homologyMap (P.mapShortComplex.map f) ≫ leftExactHomologyComparison S₂ P =
      leftExactHomologyComparison S₁ P ≫ P.map (homologyMap f) := by
  apply (cancel_epi (S₁.map P).homologyπ).1
  erw [← Category.assoc, homologyπ_naturality, Category.assoc,
    leftExactHomologyComparison_π, leftExactHomologyComparison_π_assoc,
    ← P.map_comp, homologyπ_naturality, P.map_comp,
    ← Category.assoc, leftExactCyclesComparison_naturality]
  simp only [homologyπ, P.map_comp, Category.assoc]
end CategoryTheory.ShortComplex
