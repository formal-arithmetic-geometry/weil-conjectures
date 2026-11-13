/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.ShiftedKoszulAugmentation
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnitPerfect
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnitIso

/-! # Powers Koszul complexes are perfect on a principal-open cover

Source: Stacks Project, Tag 08CX, Section 36.9.
-/

@[expose] public section

universe a b

open CategoryTheory

namespace AlgebraicGeometry

/-- The object associated to the shifted Koszul complex on powers of a finite
sequence is perfect; its canonical augmentation restricts to an isomorphism on
the union of the principal opens. Source: Stacks, Tag 08CX. -/
theorem affine_perfect_koszul_principal_unit
    (A : Type a) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (he : 1 ≤ e)
    [HasDerivedCategory.{b}
      (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{b}
        (SheafOfModules.{a} ((moduleRings (Spec (.of A)).toRingedSpace).over U))] :
    Scheme.IsPerfect (Spec (.of A))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
          (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
          (shiftedKoszulComplex A r (fun i ↦ f i ^ e)))) ∧
      IsIso (((SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace)
        (⨆ i : Fin r, (Spec (.of A)).basicOpen
          ((Scheme.ΓSpecIso (.of A)).inv (f i)))).mapDerivedCategory).map
            (affineKoszulAugmentation A r (fun i ↦ f i ^ e))) := by
  exact ⟨affine_perfect_koszul_principal_unit_perfect A r f e,
    affine_perfect_koszul_principal_unit_iso A r f e he⟩

end AlgebraicGeometry
