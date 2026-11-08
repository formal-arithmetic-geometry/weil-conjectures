/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.CategoryTheory.Sites.EpiMono
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Local null-homotopies into acyclic etale complexes

Source: Stacks Project, Cohomology on Sites, Tag 08FP, assertion (1).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

private structure AboveHomotopy
    {C : Type*} [Category C] [Preadditive C]
    {E F : CochainComplex C ℤ} (α : E ⟶ F) (k : ℤ) where
  h : Cochain E F (-1)
  comm : ∀ n : ℤ, k < n →
    α.f n = E.d n (n + 1) ≫ h.v (n + 1) n (by omega) +
      h.v n (n - 1) (by omega) ≫ F.d (n - 1) n

private def AboveHomotopy.map
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    {E F : CochainComplex C ℤ} {α : E ⟶ F} {k : ℤ}
    (H : AboveHomotopy α k) (R : C ⥤ D) [R.Additive] :
    AboveHomotopy ((R.mapHomologicalComplex (.up ℤ)).map α) k where
  h := H.h.map R
  comm n hn := by
    change R.map (α.f n) = _
    rw [H.comm n hn, R.map_add, R.map_comp, R.map_comp]
    simp only [Cochain.map_v]
    rfl

end AlgebraicGeometry
