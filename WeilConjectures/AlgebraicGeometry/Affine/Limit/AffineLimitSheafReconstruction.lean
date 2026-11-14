/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLimitSheafApproximation.AffineLimitSheafApproximation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic

import WeilConjectures.AlgebraicGeometry.Affine.Limit.AffineLimitSheafApproximationEpi
import WeilConjectures.AlgebraicGeometry.Affine.Limit.AffineLimitSheafApproximationGermKernel
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Reconstruction of abelian étale sheaves at an affine inverse limit
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every abelian étale sheaf on an affine inverse limit is the filtered colimit of
pullbacks of its direct images to the stages. -/
theorem nonempty_isColimit_affineLimitSheafApproximation
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Cone D) (hs : IsLimit s)
    (F : Sheaf s.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty (IsColimit
      (Etale.AffineLimitSheafApproximation.approximationCocone D s F)) := by
  classical
  let A := Etale.AffineLimitSheafApproximation.approximationDiagram D s F
  let c := Etale.AffineLimitSheafApproximation.approximationCocone D s F
  let q := Etale.AffineLimitSheafApproximation.approximationComparison D s F
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hmono : Mono q := by
    constructor
    intro G a b hab
    apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro x
    let P : Sheaf s.pt.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
      (pointSmallEtale (s.pt.algClosurePoint x)).sheafFiber
    have hP : Mono (P.map q) := by
      rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨i, t, rfl⟩ := Concrete.isColimit_exists_rep (A ⋙ P)
        (isColimitOfPreserves P (colimit.isColimit A)) y
      have ht : P.map (c.ι.app i) t = 0 := by
        rw [← colimit.ι_desc c i]
        change P.map (colimit.ι A i ≫ q) t = 0
        rw [P.map_comp, ConcreteCategory.comp_apply]
        exact hy
      obtain ⟨j, f, hf⟩ :=
        affineLimitSheafApproximation_germ_eventually_zero D s hs F x i t ht
      change P.map (colimit.ι A i) t = 0
      rw [← colimit.w A f, P.map_comp, ConcreteCategory.comp_apply, hf, map_zero]
    apply (cancel_mono (P.map q)).mp
    simpa only [P.map_comp] using congrArg P.map hab
  have : Epi q := epi_affineLimitSheafApproximationComparison D s hs F
  have : IsIso ((colimit.isColimit A).desc c) := isIso_of_mono_of_epi q
  exact ⟨IsColimit.ofPointIso (colimit.isColimit A)⟩

end AlgebraicGeometry.Scheme
