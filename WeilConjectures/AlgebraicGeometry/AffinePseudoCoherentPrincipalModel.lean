/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentPrincipalSheafModel
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # A module model on one principal open

Source: Stacks Project, Tag 08E7, local-model comparison in the converse direction.
-/

@[expose] public section

universe u wX wL

open CategoryTheory

namespace AlgebraicGeometry

/-- A bounded-above finite-free sheaf model on an open neighbourhood gives a
pseudo-coherent localized module complex on every principal open contained in it.

Source: Stacks Project, Tag 08E7, local-model comparison, using the affine derived
comparison of Tag 06Z0. -/
theorem affine_pseudoCoherent_principal_model (A : Type u) [CommRing A]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A)
    [HasDerivedCategory.{wL} (ModuleCat.{u} (Localization.Away f))]
    (U : (Spec (.of A)).Opens)
    (hf : PrimeSpectrum.basicOpen f ≤ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings (Spec (.of A)).toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hiso : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M)) ≅
      DerivedCategory.Q.obj P)) :
    DerivedCategory.IsPseudoCoherent
      (DerivedCategory.Q.obj ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away f)))
        (ComplexShape.up ℤ)).obj M)) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))
  obtain ⟨E, b, hbound, hfreeE, ⟨hmodel⟩⟩ :=
    affine_pseudoCoherent_principal_sheaf_model A M f U hf P hb hfree hiso
  obtain ⟨e, ⟨α⟩, _, _, _⟩ :=
    exists_affineQCohDerivedEquivalence (Localization.Away f)
  let F := e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of (Localization.Away f)))).ι
  let L := (Functor.mapHomologicalComplex
    (ModuleCat.extendScalars (algebraMap A (Localization.Away f)))
    (ComplexShape.up ℤ)).obj M
  have h : F.obj (DerivedCategory.Q.obj E) ≅ F.obj (DerivedCategory.Q.obj L) :=
    α.app E ≪≫ hmodel ≪≫ (α.app L).symm
  exact ⟨E, b, hbound, hfreeE, ⟨F.preimageIso h⟩⟩

end AlgebraicGeometry
