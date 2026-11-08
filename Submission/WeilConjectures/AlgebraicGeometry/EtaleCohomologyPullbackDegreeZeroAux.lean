/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Single

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale

private theorem exists_resolution_comparison
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K J I : CochainComplex C ℤ} (t : K ⟶ J) (s : K ⟶ I)
    [QuasiIso t] [QuasiIso s] [I.IsKInjective] :
    ∃ a : J ⟶ I, QuasiIso a ∧ Nonempty (Homotopy (t ≫ a) s) := by
  let P := HomotopyCategory.quotient C (.up ℤ)
  let b := inv (DerivedCategory.Q.map t) ≫ DerivedCategory.Q.map s
  obtain ⟨a', ha'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (P.obj J) I).2
    ((DerivedCategory.quotientCompQhIso C).hom.app J ≫ b ≫
      (DerivedCategory.quotientCompQhIso C).inv.app I)
  obtain ⟨a, rfl⟩ := P.map_surjective a'
  have ha : DerivedCategory.Q.map a = b := by
    rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app J)]
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality, ha']
    simp
  have : IsIso (DerivedCategory.Q.map a) := by rw [ha]; dsimp [b]; infer_instance
  refine ⟨a, (DerivedCategory.isIso_Q_map_iff_quasiIso C a).1 this, ⟨?_⟩⟩
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective (P.obj K) I).1
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app I)).1
  change DerivedCategory.Qh.map (P.map (t ≫ a)) ≫ _ =
    DerivedCategory.Qh.map (P.map s) ≫ _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality]
  simp [Functor.map_comp, ha, b]

end AlgebraicGeometry.Etale
