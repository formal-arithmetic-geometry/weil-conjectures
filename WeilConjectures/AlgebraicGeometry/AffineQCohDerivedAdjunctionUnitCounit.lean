/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic

import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import WeilConjectures.AlgebraicGeometry.AffineDerivedCounitHomologyFactorization

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- The affine derived adjunction has invertible unit and counit.
Source: Stacks Project, Tag 06Z0, proof after the elucidation. -/
theorem affineQCohDerivedAdjunction_unit_counit (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
    (G : schemeDerivedQCohCategory (Spec (.of A)) ⥤ DerivedCategory (ModuleCat.{u} A))
    (adj : F ⊣ G)
    (hF : Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q))
    (hG : Nonempty (G ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor)) :
    (∀ M, IsIso (adj.unit.app M)) ∧ (∀ K, IsIso (adj.counit.app K)) := by
  have hcounit (K) : IsIso (adj.counit.app K) := by
    suffices h : IsIso ((schemeDerivedQCohProperty (Spec (.of A))).ι.map
        (adj.counit.app K)) from isIso_of_reflects_iso _
          (schemeDerivedQCohProperty (Spec (.of A))).ι
    apply (DerivedCategory.isIso_iff _ _).2
    intro n
    obtain ⟨e, he⟩ := affineDerivedCounit_homology_factorization A F G adj hF hG K n
    have := K.property n
    have : IsIso (C := SheafOfModules.{u}
        (moduleRings (Spec (.of A)).toRingedSpace))
        (Scheme.Modules.fromTildeΓ (R := .of A)
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj K.obj)) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) _
    rw [he]
    infer_instance
  have hreflect {M N : DerivedCategory (ModuleCat.{u} A)} (f : M ⟶ N)
      (hf : IsIso (F.map f)) : IsIso f := by
    apply (DerivedCategory.isIso_iff _ f).2
    intro n
    obtain ⟨e⟩ := affineDerivedTilde_homology_comparison A F hF n
    have hmap : IsIso (((F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).map f) := by
      change IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((schemeDerivedQCohProperty (Spec (.of A))).ι.map (F.map f)))
      infer_instance
    have htilde := (NatIso.isIso_map_iff e f).1 hmap
    change IsIso ((tilde.functor (.of A)).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map f)) at htilde
    let := (tilde.fullyFaithfulFunctor (R := .of A)).reflectsIsomorphisms
    exact isIso_of_reflects_iso _ (tilde.functor (.of A))
  refine ⟨?_, hcounit⟩
  intro M
  have := hcounit (F.obj M)
  apply hreflect
  exact isIso_of_comp_hom_eq_id _ (adj.left_triangle_components M)

end AlgebraicGeometry
