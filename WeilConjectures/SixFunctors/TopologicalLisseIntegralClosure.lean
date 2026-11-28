/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTopologicalLisseFiltration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalStratifiedLatticeData

/-! Lattice filtration step for topological Noetherian integral generators.

## Implementation details

A locally free module over the continuous `E`-coefficients on a topologically Noetherian
scheme has integral lattices on the strata of a finite locally closed stratification. The
open-prefix filtration of `v_! t_* L` along a refinement of this stratification to `X` has
graded pieces that are zero or scalar extensions of integral generators, so `v_! t_* L`
lies in every triangulated, isomorphism-closed property containing the generators.

## References

* Bhatt--Scholze, Lemma 6.8.13, Proposition 6.8.14(2)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.SixFunctors

/-- A locally free module over the continuous `E`-coefficients on a topologically Noetherian
scheme has stratified lattice models over the continuous valuation ring of `E`. -/
theorem stratifiedLatticeModels_integralScalarMap (ℓ : ℕ) [Fact ℓ.Prime] (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) T))
    (hL : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj E) T) L) :
    CondensedRing.StratifiedLatticeModels (CondensedRing.integralCoeff ℓ E)
      (Profinite.continuousMapRingObj E) (CondensedRing.integralScalarMap ℓ E) L := by
  obtain ⟨R, hR⟩ := CondensedRing.exists_topologicalStratifiedLatticeData ℓ E T L hL
  refine ⟨R, fun i ↦ ?_⟩
  obtain ⟨M, hM, ι, -, hι⟩ := hR i
  exact ⟨M, hM, ⟨@asIso _ _ _ _ _ hι⟩⟩

/-- A lisse finite-coefficient extension `v_! t_* L` belongs to the triangulated,
isomorphism-closed closure of the integral locally free generators. -/
theorem topological_lisse_integral_closure
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (T V : Scheme.{u}) (t : T ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion t] [IsOpenImmersion v]
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (finiteCoefficientObject T ℓ E))
    (hL : IsLocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj E.1) T) L) :
    (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
      P.IsClosedUnderIsomorphisms})
      ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.openImmersionLowerShriek (Profinite.continuousMapRingObj E.1) v).obj
          ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1) t).obj L))) := by
  rw [unary_relation_sInf_iff]
  rintro P ⟨hP, htri, hiso⟩
  have : TopologicalSpace.NoetherianSpace T := (t ≫ v).isEmbedding.isInducing.noetherianSpace
  have hR : CondensedRing.StratifiedLatticeModels (Profinite.padicIntegersRingObj ℓ E.1)
      (Profinite.continuousMapRingObj E.1)
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) L := by
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
    let : NormedAlgebra ℚ_[ℓ] E.1 :=
      { norm_smul_le c x := by
          change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
            ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
            PadicAlgCl.norm_extends] }
    exact stratifiedLatticeModels_integralScalarMap ℓ E.1 T L hL
  refine CondensedRing.closedOpenExtension_mem_of_stratifiedLatticeModels
    (Profinite.padicIntegersRingObj ℓ E.1) (Profinite.continuousMapRingObj E.1)
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) X P ?_ t v L hR
  intro Y d hd M hM
  have : TopologicalSpace.NoetherianSpace Y := d.isEmbedding.isInducing.noetherianSpace
  exact hP _ ⟨Y, d.image, d.toImage, d.imageι, inferInstance, inferInstance, M, hM, rfl⟩

end WeilConjectures.SixFunctors
