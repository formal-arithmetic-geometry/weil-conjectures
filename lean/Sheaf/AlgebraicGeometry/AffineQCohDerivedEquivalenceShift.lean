module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- The affine equivalence sends the shifted free rank-one module to the shifted
structure sheaf. This is the shift-normalization part of Tag 06Z0.
Source: Stacks Project, Derived Categories of Schemes, Lemma 36.3.5, Tag 06Z0
(blueprint: new-affine-qcoh-derived-equivalence-shift).
The proof identifies the degree-zero tilde of `A` with the structure sheaf and
then transports this isomorphism through the shift functor. -/
theorem affineQCohDerivedEquivalence_shift (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (e : DerivedCategory (ModuleCat.{u} A) ≌ schemeDerivedQCohCategory (Spec (.of A)))
    (hcomp : Nonempty (DerivedCategory.Q ⋙ e.functor ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q))
    (htri : ∃ (_h : (e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).CommShift ℤ),
        (e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).IsTriangulated) :
      ∀ k : ℤ, Nonempty
        ((e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).obj
          (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A A))⟦k⟧) ≅
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)))⟦k⟧) := by
  sorry

end AlgebraicGeometry
