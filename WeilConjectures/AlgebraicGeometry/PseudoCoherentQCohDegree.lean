/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! A single-degree reduction of quasi-coherent cohomology for pseudo-coherent complexes.

## References

* [Stacks, Tag 08E5]
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem qc_over_inverse (Y : Scheme.{u}) (U : Y.Opens)
    (M : U.toScheme.Modules) [M.IsQuasicoherent] :
    ((Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  have (V : CategoryTheory.Over U) :
      (CategoryTheory.Over.post (X := V) U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology Y).over U).over V)
        ((Opens.grothendieckTopology (↥U)).over _) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      (CategoryTheory.CoverPreserving.overPost V
        (Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.functor))
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    U.overEquivalence.functor _
    (U.sheafOfModulesEquivOverInverseUnit Y.ringCatSheaf)

private theorem qc_homology (Y : Scheme.{u})
    (P : CochainComplex Y.Modules ℤ) (hP : ∀ i, (P.X i).IsQuasicoherent) (n : ℤ) :
    (P.homology n).IsQuasicoherent := by
  have : (P.sc n).X₁.IsQuasicoherent := hP _
  have : (P.sc n).X₂.IsQuasicoherent := hP _
  have : (P.sc n).X₃.IsQuasicoherent := hP _
  have := Modules.isQuasicoherent_kernel (P.sc n).g
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (P.sc n).homologyIsoCokernelLift.symm
    (Modules.isQuasicoherent_cokernel
      (CategoryTheory.Limits.kernel.lift (P.sc n).g (P.sc n).f (P.sc n).zero))

set_option backward.isDefEq.respectTransparency false in
private theorem qc_local_free_homology (Y : Scheme.{u}) (U : Y.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ)
    (hP : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin r)))) (n : ℤ) :
    (P.homology n).IsQuasicoherent := by
  let F := (Modules.overEquiv U).functor
  let C := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hC (i : ℤ) : (C.X i).IsQuasicoherent := by
    obtain ⟨r, ⟨e⟩⟩ := hP i
    exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (F.mapIso e ≪≫
        (SheafOfModules.mapFreeIso F (ULift.{u} (Fin r))
          (Modules.overEquivFunctorObjUnitIso U)).symm).symm
      (SheafOfModules.isQuasicoherent_free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))
  have hhom : (C.homology n).IsQuasicoherent := qc_homology U.toScheme C hC n
  have : (F.obj (P.homology n)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((F.mapHomologicalComplexHomologyIso (.up ℤ) n).app P) hhom
  have hinv := qc_over_inverse Y U (F.obj (P.homology n))
  exact (SheafOfModules.isQuasicoherent ((moduleRings Y.toRingedSpace).over U)).prop_of_iso
    ((Modules.overEquiv U).unitIso.app (P.homology n)).symm hinv

set_option backward.isDefEq.respectTransparency false in
/-- A fixed cohomology sheaf of a pseudo-coherent derived object is quasi-coherent.
(Stacks, Tag 08E5) -/
theorem schemeDerivedQCohProperty_of_isPseudoCoherent_degree
    (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (E : schemeDerivedCategory Y) (hE : IsPseudoCoherent Y E) (n : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E).IsQuasicoherent := by
  classical
  choose U hy P _hb hf he using hE
  let H := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E
  have hlocal (y : Y) : (H.over (U y)).IsQuasicoherent := by
    let F := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) (U y)
    let D := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over (U y))
    obtain ⟨e⟩ := he y
    have hhom := qc_local_free_homology Y (U y) (P y) (hf y) n
    exact (SheafOfModules.isQuasicoherent ((moduleRings Y.toRingedSpace).over (U y))).prop_of_iso
      (((F.mapDerivedCategoryHomologyFunctorIso n).app E) ≪≫
        (DerivedCategory.homologyFunctor D n).mapIso e ≪≫
        ((DerivedCategory.homologyFunctorFactors D n).app (P y))).symm hhom
  apply SheafOfModules.IsQuasicoherent.of_coversTop H U
  apply (Opens.coversTop_iff _ U).mpr
  apply eq_top_iff.mpr
  intro y _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩

end AlgebraicGeometry.Scheme
