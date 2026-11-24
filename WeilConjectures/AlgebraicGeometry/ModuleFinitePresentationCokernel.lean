/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationCokernelKernel
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Finite presentation of cokernels on a ringed space

## Main statements

- `AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_isFiniteType`:
  finite-type source and finitely presented target give a finitely presented cokernel.
- `AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_both_isFinitePresentation`:
  the special case where both source and target are finitely presented.

## References

* [Stacks, Tag 0H96](https://stacks.math.columbia.edu/tag/0H96)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

-- Stacks 0H96, final step: refine the cover using finite generators of the kernel.
-- Reuses the proved construction from CoherentFiniteTypeLocallyNoetherian.lean.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem isFinitePresentation_of_generators_kernel
    {C : Type u} [SmallCategory C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) (G : M.GeneratingSections)
    [G.IsFiniteType] [(kernel G.π).IsFiniteType] : M.IsFinitePresentation := by
  classical
  obtain ⟨r, hr⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (kernel G.π)
  let H (j : r.I) := SheafOfModules.overFunctor R (r.X j)
  have (j : r.I) : PreservesColimitsOfSize.{u, u} (H j) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward (F := Over.forget (r.X j)) (𝟙 (R.over (r.X j)))))
  let e (j : r.I) := SheafOfModules.mapFreeIso (H j) G.I (Iso.refl _)
  let a (j : r.I) := (r.generators j).π ≫ (H j).map (kernel.ι G.π) ≫ (e j).inv
  let b (j : r.I) := (G.map (H j) (Iso.refl _)).π
  have hab (j : r.I) : a j ≫ b j = 0 := by
    dsimp only [a, b]
    rw [SheafOfModules.GeneratingSections.map_π_eq]
    simp only [e, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
      kernel.condition, Functor.map_zero, comp_zero]
  have hcol (j : r.I) : IsColimit (CokernelCofork.ofπ (b j) (hab j)) := by
    let c := CokernelCofork.ofπ G.π (kernel.condition G.π)
    have hc : IsColimit c := Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι G.π) (kernel.condition G.π))
      (kernelIsKernel _)
    have hh : ((H j).map (kernel.ι G.π) ≫ (e j).inv) ≫ b j = 0 := by
      dsimp only [b]
      rw [SheafOfModules.GeneratingSections.map_π_eq]
      simp only [e, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
        kernel.condition, Functor.map_zero]
    let c' := CokernelCofork.ofπ (b j) hh
    have hc' : IsColimit c' := IsCokernel.ofIso _ (c.mapIsColimit hc (H j)) c'
      (Iso.refl _) (e j).symm (Iso.refl _) (by simp)
      (by
        simp only [c', CokernelCofork.π_ofπ, b, e,
          SheafOfModules.GeneratingSections.map_π_eq, Iso.symm_hom,
          Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
        rfl)
    exact isCokernelEpiComp hc' (r.generators j).π rfl
  let D : M.QuasicoherentData :=
    { I := r.I
      X := r.X
      coversTop := r.coversTop
      presentation j := SheafOfModules.presentationOfIsCokernelFree (a j) (b j)
        (hab j) (hcol j) }
  have : D.IsFinitePresentation := ⟨fun j ↦ by
    have := hr.isFiniteType j
    exact ⟨⟨inferInstanceAs (Finite G.I)⟩,
      ⟨inferInstanceAs (Finite (r.generators j).I)⟩⟩⟩
  exact D.isFinitePresentation

/-- The cokernel of a map from a finite-type module sheaf to a finitely presented module sheaf
on a ringed space is finitely presented (Stacks, Tag 0H96). -/
theorem isFinitePresentation_cokernel_of_isFiniteType
    (X : RingedSpace.{u}) {G H : SheafOfModules.{u} (moduleRings X)}
    (f : G ⟶ H) [G.IsFiniteType] [H.IsFinitePresentation] :
    (cokernel f).IsFinitePresentation := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData H
  have hfp (i : q.I) : ((cokernel f).over (q.X i)).IsFinitePresentation := by
    let P := q.presentation i
    let F := SheafOfModules.overFunctor (moduleRings X) (q.X i)
    let g := P.generators.π ≫ F.map (cokernel.π f)
    have : Epi g := inferInstanceAs (Epi (P.generators.π ≫ F.map (cokernel.π f)))
    let S := SheafOfModules.GeneratingSections.ofEpiFree g
    have : P.IsFinite := hq.isFinite_presentation i
    have : S.IsFiniteType := ⟨inferInstanceAs (Finite P.generators.I)⟩
    have : (kernel S.π).IsFiniteType := by
      simpa only [S, SheafOfModules.GeneratingSections.ofEpiFree_π] using
        kernel_composite_cokernel_isFiniteType X (q.X i) f P
    exact isFinitePresentation_of_generators_kernel ((cokernel f).over (q.X i)) S
  exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
    (cokernel f) q.I q.X q.coversTop hfp

/-- The cokernel of a map between finitely presented module sheaves on a ringed space is
finitely presented (Stacks, Tag 0H96). -/
theorem isFinitePresentation_cokernel_of_both_isFinitePresentation
    (X : RingedSpace.{u}) {G H : SheafOfModules.{u} (moduleRings X)}
    (f : G ⟶ H) [G.IsFinitePresentation] [H.IsFinitePresentation] :
    (cokernel f).IsFinitePresentation := by
  exact isFinitePresentation_cokernel_of_isFiniteType X f

end AlgebraicGeometry.RingedSpace
