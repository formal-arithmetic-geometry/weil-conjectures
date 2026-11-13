/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.LocalKoszulAugmentedCarrier
import WeilConjectures.AlgebraicGeometry.LocalKFlatTensorRoof
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.RingTheory.KoszulProjectiveResolution
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Local zero-differential tensor models

## References

* [Stacks, Tags 0BQY and 068C]
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The tensor pullback has a local finite-free zero model (Stacks, Tags 0BQY and 068C). -/
theorem local_tensor_has_finite_free_zero_model
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (_hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a)
    (_hflat : ∀ k : ℤ, SheafOfModules.IsFlat (P.X k)) :
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    ∀ (V : Z.Opens) (U : Y.affineOpens)
      (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f),
      HasFiniteFreeZeroModel
        (V.toScheme.ringCatSheaf.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)))
        ((moduleOpenOverComplexFunctor Z V (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))).obj T) := by
  dsimp only
  intro V U hU
  obtain ⟨m, f, hf, hreg⟩ := hU
  obtain ⟨Q, hQ⟩ := ExteriorAlgebra.exists_koszul_projective_resolution
    (Γ(Y, U.1) : Type u) (i.ker.ideal U) m f hreg hf
  obtain ⟨K, b, hK, hzero, hbound, hfree⟩ :=
    exists_local_koszul_augmented_carrier i V U m f hf Q hQ
  let F := (Scheme.Modules.restrictFunctor U.1.ι).mapHomologicalComplex (.up ℤ)
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.1.ι) := inferInstance
  have : PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.1.ι) := inferInstance
  have : (Scheme.Modules.restrictFunctor U.1.ι).PreservesHomology := inferInstance
  have : QuasiIso a := _hP.1
  have hPa : CochainComplex.IsKFlatTensorResolution (R := U.1.toScheme.sheaf) (F.map a) :=
    by
      refine ⟨?_, isKFlat_restrict U.1.ι P _hP.2⟩
      change QuasiIso
        (((Scheme.Modules.restrictFunctor U.1.ι).mapHomologicalComplex (.up ℤ)).map a)
      infer_instance
  obtain ⟨L, q, p, hq, hp⟩ :=
    exists_local_kflat_tensor_roof i V U.1 P K _ (F.map a) b hPa hK
  exact ⟨_, L, q, p, hq, hp, hzero, hbound, hfree⟩

end AlgebraicGeometry
