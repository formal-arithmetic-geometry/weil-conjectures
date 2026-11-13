/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Group.Finsupp
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.LinearAlgebra.SemilinearFrobenius

import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierPrimeBaseChangeModel
import WeilConjectures.AlgebraicGeometry.Curve.ConstantModCohomologyFinsuppPullback

@[expose] public section

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- The characteristic-p degree-one comparison has an Artin--Schreier fixed-point model.
Source: Stacks Project, Tag 0A3P, proof, and Tag 02KH; arbitrary coefficients use
`Etale.exists_constantModSheaf_finite_sum_colimit` and
`Scheme.sheafH_isColimit_large_filtered` (Tags 03Q5 and 0739). -/
theorem exists_constantModSheaf_one_frobenius_baseChange_model
    {Λ : Type (u + 1)} [CommRing Λ] {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] [ConnectedSpace C] [IsProper f]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :
    ∃ (V : ModuleCat.{u + 1} k) (_ : FiniteDimensional k V)
      (F : V →ₛₗ[frobenius k p] V)
      (F' : (k' ⊗[k] V) →ₛₗ[frobenius k' p] (k' ⊗[k] V))
      (hF' : ∀ v : V, F' (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] F v) (I : Type (u + 1))
      (e : Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (Etale.constantModSheaf Λ C p)) 1 ≃+ (I →₀ LinearMap.Frobenius.fixedPoints F))
      (e' : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} ι').obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (Etale.constantModSheaf Λ C p))) 1 ≃+
        (I →₀ LinearMap.Frobenius.fixedPoints F')),
      ∀ x i, e' (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (Etale.constantModSheaf Λ C p)) 1 x) i =
        (⟨1 ⊗ₜ[k] (e x i : V), by
          rw [LinearMap.Frobenius.mem_fixedPoints, hF',
            LinearMap.Frobenius.mem_fixedPoints.mp (e x i).2]⟩ :
          LinearMap.Frobenius.fixedPoints F') := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated f
  have : IsProper f' := MorphismProperty.of_isPullback h inferInstance
  have : CompactSpace C' := QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiSeparatedSpace C' := quasiSeparatedSpace_of_quasiSeparated f'
  obtain ⟨V, hd, F, F', hF', e, e', he⟩ :=
    exists_constantZMod_one_frobenius_baseChange_model f p h
  obtain ⟨I, a, b, hab⟩ :=
    Etale.exists_constantModSheaf_cohomology_finsupp_pullback Λ ι' p 1
  refine ⟨V, hd, F, F', hF', I,
    a.trans (Finsupp.mapRange.addEquiv e),
    b.trans (Finsupp.mapRange.addEquiv e'), ?_⟩
  intro x i
  simp only [AddEquiv.trans_apply, Finsupp.mapRange.addEquiv_apply,
    Finsupp.mapRange_apply]
  rw [hab]
  exact he (a x i)

end AlgebraicGeometry.IsCurve
