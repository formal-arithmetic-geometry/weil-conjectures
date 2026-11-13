/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.RingTheory.KoszulDualComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import WeilConjectures.AlgebraicGeometry.AffineKoszulHomComplexIso
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Affine coordinates for the sheafified Koszul Hom complex

## References

* Stacks Project, Tag 0BQZ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The cohomology of Hom from the sheafified Koszul complex into the structure
sheaf is the associated sheaf of the recorded signed dual Koszul homology
(Stacks, Tags 0BQZ and 01HV). -/
theorem affine_koszul_hom_coordinates
    {Y : Scheme.{u}} (U : Y.affineOpens) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (q : ℤ) :
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) n f).extend
        ComplexShape.embeddingDownNat)
    Nonempty ((homComplex (R := U.1.toScheme.toRingedSpace.sheaf) E
      ((CochainComplex.singleFunctor U.1.toScheme.Modules 0).obj
        (SheafOfModules.unit U.1.toScheme.ringCatSheaf))).homology q ≅
      T.obj ((ExteriorAlgebra.koszulDualCochainComplex
        (Γ(Y, U.1) : Type u) n f).homology q)) := by
  let A := (Γ(Y, U.1) : Type u)
  let T := tilde.functor Γ(Y, U.1)
  let R := Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let F := T ⋙ R
  let : PreservesFiniteLimits T := tilde_preserves_finite_limits A
  let : PreservesFiniteLimits R := by dsimp [R]; infer_instance
  let : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  let : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  obtain ⟨e⟩ := affine_koszul_hom_complex_iso U n f
  exact ⟨(HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q).mapIso e ≪≫
    (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) q).app
      (ExteriorAlgebra.koszulDualCochainComplex A n f)⟩

end AlgebraicGeometry
