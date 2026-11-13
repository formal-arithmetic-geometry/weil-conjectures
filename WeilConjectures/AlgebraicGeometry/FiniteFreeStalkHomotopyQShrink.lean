/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMapEquality
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Shrinking equality for a single finite free complex
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A stalk homotopy of single-complex maps spreads inside a prescribed neighbourhood. -/
theorem exists_shrink_homotopy_Q_inside_of_stalk
    {Y : Scheme.{u}}
    (i : ℤ) (r : ℕ) (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (c e : (((restrictFunctor V.ι).mapHomologicalComplex _).obj
      ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))) ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj
      ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))))
    (hQ : Nonempty (Homotopy
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map c)
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map e)))
    (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U) :
    ∃ (W : Y.Opens) (hWU : W ≤ U), y ∈ W ∧
      Nonempty (Homotopy
        (((restrictFunctor (Y.homOfLE (hWU.trans hUV))).mapHomologicalComplex _).map c)
        (((restrictFunctor (Y.homOfLE (hWU.trans hUV))).mapHomologicalComplex _).map e)) := by
  obtain ⟨h⟩ := hQ
  have hi : (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map (c.f i) =
      (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map (e.f i) := by
    simpa [dNext, prevD,
      Functor.mapHomologicalComplex, HomologicalComplex.single_obj_d] using h.comm i
  obtain ⟨W, hWU, hyW, heq⟩ := exists_restrict_eq_of_pullback_eq
    r y V hyV _ _
    ⟨(restrictFunctor V.ι).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i _)⟩
    (c.f i) (e.f i) hi U hUV hyU
  refine ⟨W, hWU, hyW, ⟨Homotopy.ofEq ?_⟩⟩
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = i
  · subst n
    exact heq
  · exact ((restrictFunctor (Y.homOfLE (hWU.trans hUV))).map_isZero
      ((restrictFunctor V.ι).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i _ n hn))).eq_of_src _ _


end AlgebraicGeometry.Scheme.Modules
