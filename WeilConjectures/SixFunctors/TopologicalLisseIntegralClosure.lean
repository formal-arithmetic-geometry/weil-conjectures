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
Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.14(2), together with the
ordered lattice filtration in the topological Noetherian integral-model argument
(blueprint: lem-sfb-topological-lisse-integral-closure).

The missing argument constructs a finite stratified integral lattice filtration of a
lisse finite-coefficient module and identifies each quotient with an integral generator.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.SixFunctors

/-- A locally free module over the continuous `E`-coefficients on a topologically Noetherian
scheme has stratified lattice models over the continuous valuation ring of `E`.

Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph
(blueprint: lem-sfb-topological-lisse-integral-closure). -/
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
isomorphism-closed closure of the integral locally free generators.

Source: Bhatt--Scholze, Lemma 6.8.13 (first paragraph) and Proposition 6.8.14(2);
steps 1 and 3 of the plan of lem-sfb-topological-integral-generators
(blueprint: lem-sfb-topological-lisse-integral-closure).

Proof:
1. `T` is topologically Noetherian, as a subspace of `X`. By
   lem-sfb-topological-stratified-lattices choose an ordered finite stratification
   `T = ⊔ T_k` with opens `U_k = T_1 ∪ ... ∪ T_k` (`u_k : U_k → T`, `b_k : T_k → T`,
   `c_k : T_k → U_k` closed) and `O_E`-lattices `L_{0,k} ⊆ b_k^* L` with
   `E ⊗ L_{0,k} ≅ b_k^* L`.
2. Put `L_k = u_{k!} u_k^* L`. The open-closed localization sequence
   (lem-weil-pbc-proetale-ringed-open-closed) makes `L_{k-1} → L_k` monic, and by
   lem-sfb-open-filtration-successor `L_k / L_{k-1} ≅ u_{k!} c_{k*} (b_k^* L)`, with
   `L_0 = 0` and `L_m = L`.
3. `v_!` and `t_*` are exact, so applying them gives a finite filtration of `v_! t_* L`;
   by the composition comparisons of lem-sfb-topological-locally-closed-extension each
   quotient is `a_{k!}(b_k^* L)` for the locally closed `a_k : T_k → X`, written as an
   open immersion followed by a closed immersion (all opens are quasi-compact by
   lem-sfb-noetherian-space-compact-subsets).
4. `E_X` is flat over `O_{E,X}` (det-prop-sfb-qlbar-colimit-x-invert-ell), and the open and
   closed projection formulas (lem-sfb-condensed-support-projection-formula) give
   `E ⊗ a_{k!} L_{0,k} ≅ a_{k!}(E ⊗ L_{0,k}) ≅ a_{k!}(b_k^* L)`: each quotient in degree
   zero is isomorphic to an integral generator.
5. Each short exact sequence of the filtration is a distinguished triangle
   (lem-sf-derived-ses-triangle); induction on `k`, starting from the zero object, puts
   `v_! t_* L [0]` in the closure. -/
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
