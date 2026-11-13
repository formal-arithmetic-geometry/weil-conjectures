/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.AffinePrincipalSheafComplexTransport
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeSheafComplexLift

/-! A finite-free witness for the local principal-open pseudo-coherence comparison.
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite-free module complex whose associated sheaf is the principal-open model.
Source: Stacks Project, Tag 08E7, converse proof, local-model comparison. -/
theorem affine_pseudoCoherent_principal_sheaf_model (A : Type u) [CommRing A]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A)
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))]
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
    ∃ E : CochainComplex (ModuleCat.{u} (Localization.Away f)) ℤ,
      ∃ b : ℤ, E.IsStrictlyLE b ∧
        (∀ j : ℤ, Module.Free (Localization.Away f) (E.X j) ∧
          Module.Finite (Localization.Away f) (E.X j)) ∧
        Nonempty (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Localization.Away f))
            (SheafOfModules.{u}
              (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))
            _ _ _ _ (tilde.functor (.of (Localization.Away f)))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj E) ≅
          DerivedCategory.Q.obj
            ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Localization.Away f))
              (SheafOfModules.{u}
                (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))
              _ _ _ _ (tilde.functor (.of (Localization.Away f)))
              ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
                ((Functor.mapHomologicalComplex
                  (ModuleCat.extendScalars (algebraMap A (Localization.Away f)))
                  (ComplexShape.up ℤ)).obj M))) := by
  obtain ⟨C, hCbound, hCfree, ⟨eC⟩⟩ :=
    affine_principal_sheaf_complex_transport A M f U hf P hb hfree hiso
  obtain ⟨E, b, hEbound, hEfree, ⟨eE⟩⟩ :=
    affine_finiteFree_sheaf_complex_lift (Localization.Away f) C hCbound hCfree
  exact ⟨E, b, hEbound, hEfree, ⟨DerivedCategory.Q.mapIso eE ≪≫ eC⟩⟩

end AlgebraicGeometry
