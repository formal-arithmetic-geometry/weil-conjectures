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
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# The affine quasi-coherent derived equivalence

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.3.5, Tag 06Z0.
-/

@[expose] public section

universe u wA wY

open CategoryTheory

namespace AlgebraicGeometry

/-- On `Y = Spec A`, termwise associated sheaf induces the equivalence
`D(A) ≌ D_QCoh(𝒪_Y)`. Its inverse is derived global sections, with the
`Γ(Y, 𝒪_Y)`-module structure transported to `A` through `ΓSpecIso`. The composite
with the full-subcategory inclusion is triangulated for a compatible shift structure,
and it sends `A[k]` to `𝒪_Y[k]` for every integer `k`.

Source: Stacks Project, Lemma 36.3.5, Tag 06Z0. -/
theorem exists_affineQCohDerivedEquivalence (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    ∃ e : DerivedCategory (ModuleCat.{u} A) ≌ schemeDerivedQCohCategory (Spec (.of A)),
      Nonempty (DerivedCategory.Q ⋙ e.functor ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) ∧
      Nonempty (e.inverse ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor) ∧
      (∃ (_h : (e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).CommShift ℤ),
        (e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).IsTriangulated) ∧
      ∀ k : ℤ, Nonempty
        ((e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).obj
          (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A A))⟦k⟧) ≅
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)))⟦k⟧) := by
  have hcore := exists_affineQCohDerivedEquivalence_core A
  obtain ⟨e, h1, h2, h3⟩ := hcore
  have h4 := affineQCohDerivedEquivalence_shift A e h1 h3
  exact ⟨e, h1, h2, h3, h4⟩

end AlgebraicGeometry
