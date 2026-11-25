/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.FormalModuleQuotientScalarZero
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Ideal powers in the kernel of cohomology reduction

## References

* Stacks Project, Tag 02OC
-/

@[expose] public section

universe v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Reduction modulo the extended ideal power kills that power on cohomology.
No properness, coherence or Noetherian hypothesis is needed for this assertion.
(Stacks, Theorem 02OC.) -/
theorem formalFunctions_power_le_ker {A : Type v} [CommRing A]
    (I : Ideal A) {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (p n : ℕ) :
    I ^ n • (⊤ : Submodule A
      ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙ ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F)) ≤
    LinearMap.ker ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
      (formalModuleQuotientπ J n F)).hom := by
  let C := RingedSpace.moduleCohomology X.toRingedSpace p
  let r := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  let Q := formalModuleQuotient J n F
  apply (Submodule.smul_le).2
  intro a ha x _
  apply LinearMap.mem_ker.mpr
  let y := (C.map (formalModuleQuotientπ J n F)).hom x
  have hz := moduleCohomology_scalar_endomorphism Q (0 : Q ⟶ Q) (r a)
    (fun U t ↦ by
      change 0 = _
      exact (formalModuleQuotient_scalar_zero I f J hJ F n a ha U t).symm)
    p y
  have hz₀ := moduleCohomology_scalar_endomorphism Q (0 : Q ⟶ Q) 0
    (fun U t ↦ by change 0 = _; simp) p y
  have hy : r a • y = 0 := by
    simpa only [zero_smul] using hz.symm.trans hz₀
  rw [map_smul]
  exact hy

end AlgebraicGeometry
