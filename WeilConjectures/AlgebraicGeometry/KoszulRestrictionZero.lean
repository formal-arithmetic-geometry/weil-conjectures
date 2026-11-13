/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.AlgebraicGeometry.KoszulRestrictionZeroBase
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Koszul complexes vanish on the basic-open complement

## References

* Stacks Project, Tag 09IR.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- All shifts of the sheafified Koszul complex vanish on the union of the basic opens
(Stacks, Tags 09IR, 0663). -/
theorem isZero_restrict_shift_koszul
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (n : ℤ) :
    IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj
      ((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r f).extend
              ComplexShape.embeddingDownNat)))⟦n⟧)) := by
  let L := (SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory
  let K : DerivedCategory (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) :=
    (DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        _ _ _ _ (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩
        (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat)))
  have hz : IsZero (L.obj K) := isZero_restrict_koszul_base A r f U hU
  exact (Functor.map_isZero (shiftFunctor _ n) hz).of_iso ((L.commShiftIso n).app K)

end AlgebraicGeometry
