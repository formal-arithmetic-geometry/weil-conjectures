/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkHomotopyPShrink
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkHomotopyQShrink

/-! # Shrinking to spread two specified stalk homotopies
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem homotopy_of_natIso
    {A C : Type*} [Category A] [Category C] [Preadditive C]
    {F G : A ⥤ CochainComplex C ℤ} (e : F ≅ G)
    {K L : A} (f g : K ⟶ L) (h : Homotopy (G.map f) (G.map g)) :
    Nonempty (Homotopy (F.map f) (F.map g)) := by
  have H := (h.compLeft (e.hom.app K)).compRight (e.inv.app L)
  simpa only [Category.assoc, ← e.hom.naturality_assoc,
    e.hom_inv_id_app, Category.comp_id] using Nonempty.intro H

/-- Restriction preserves homotopies, using the natural comparison for composition. -/
private theorem restrict_homotopy_P_to_subopen
    {Y : Scheme.{u}} {P : CochainComplex Y.Modules ℤ} {V U W : Y.Opens}
    {a b : (((restrictFunctor V.ι).mapHomologicalComplex _).obj P) ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)}
    (hWU : W ≤ U) (hUV : U ≤ V) (hPU : Nonempty (Homotopy
      (((restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex _).map a)
      (((restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex _).map b))) :
    Nonempty (Homotopy
      (((restrictFunctor (Y.homOfLE (hWU.trans hUV))).mapHomologicalComplex _).map a)
      (((restrictFunctor (Y.homOfLE (hWU.trans hUV))).mapHomologicalComplex _).map b)) := by
  obtain ⟨h⟩ := hPU
  let c := NatIso.mapHomologicalComplex
    ((restrictFunctorCongr (Y.homOfLE_homOfLE hWU hUV)).symm ≪≫
      restrictFunctorComp (Y.homOfLE hWU) (Y.homOfLE hUV)) (ComplexShape.up ℤ)
  exact homotopy_of_natIso c a b ((restrictFunctor (Y.homOfLE hWU)).mapHomotopy h)

/-- Two specified pairs of endomorphisms become homotopic after shrinking to a neighbourhood
of the point. -/
theorem exists_shrink_homotopy_pair_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i : ℤ) (r : ℕ) (y : Y)
    (V : Y.Opens) (hyV : y ∈ V)
    (a b : (((restrictFunctor V.ι).mapHomologicalComplex _).obj P) ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj P))
    (c e : (((restrictFunctor V.ι).mapHomologicalComplex _).obj
      ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))) ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj
      ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))))
    (hP : Nonempty (Homotopy
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map a)
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map b)))
    (hQ : Nonempty (Homotopy
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map c)
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map e))) :
    ∃ (W : Y.Opens) (hWV : W ≤ V), y ∈ W ∧
      Nonempty (Homotopy
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map a)
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map b)) ∧
      Nonempty (Homotopy
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map c)
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map e)) := by
  obtain ⟨U, hUV, hyU, hPU⟩ :=
    exists_shrink_homotopy_P_of_stalk P d hge hle hfree y V hyV a b hP
  obtain ⟨W, hWU, hyW, hQW⟩ :=
    exists_shrink_homotopy_Q_inside_of_stalk i r y V hyV c e hQ U hUV hyU
  exact ⟨W, hWU.trans hUV, hyW, restrict_homotopy_P_to_subopen hWU hUV hPU, hQW⟩

end AlgebraicGeometry.Scheme.Modules
