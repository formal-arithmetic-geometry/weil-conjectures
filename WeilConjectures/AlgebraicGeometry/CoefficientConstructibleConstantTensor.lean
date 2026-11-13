/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.AlgebraicGeometry.CoefficientConstantTensorLocalModels
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.AlgebraicGeometry.NoetherianGlobalConstructibility
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.ConstructibleSheaf.Refinement

/-! # Tensoring constructible complexes with finite constant modules

## References

* Stacks Project, Tags 09BQ and 094H
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

/-- Exact constant realization of a module in degree zero on the coefficient-sized site
(Stacks, Tags 093J and 09BQ). -/
def coefficientConstantSingle (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] (M : ModuleCat.{max v (u + 1)} A) :
    adicFiniteAmbient.{u, v} X A :=
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := constant T A
  (Q R).obj ((HomologicalComplex.single (Mod R) (.up ℤ) 0).obj
    ((commutativeSiteConstantModuleFunctor T A).obj M))

/-- The existing K-flat tensor with the specified constant module in degree zero
(Stacks, Tags 09BQ and 094H). -/
def coefficientConstantTensor (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (K : adicFiniteAmbient.{u, v} X A) (M : ModuleCat.{max v (u + 1)} A) :
    adicFiniteAmbient.{u, v} X A :=
  let R := constant (coefficientProEtaleModelTopology.{u, v} X) A
  letI := HasDerivedCategory.standard (Mod R)
  ((SheafOfModules.KFlatFixedTensor.derivedTensor R).obj K).obj
    (coefficientConstantSingle.{u, v} X A M)

private theorem finiteModels_iff_presentation
    {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type w)
    [CommRing A] [IsNoetherianRing A] (F : Sheaf J (ModuleCat A)) :
    IsCoefficientModelLocallyConstantFinite J A F ↔
      ∀ V : C, ∃ T : Sieve V, T ∈ J V ∧
        ∀ (W : C) (f : W ⟶ V), T f →
          ∃ M : ModuleCat A, Module.FinitePresentation A M ∧
            Nonempty (F.over W ≅ (constantSheaf (J.over W) (ModuleCat A)).obj M) := by
  constructor
  all_goals
    intro h V
    obtain ⟨T, hT, ht⟩ := h V
    refine ⟨T, hT, fun W f hf ↦ ?_⟩
    obtain ⟨M, hM, e⟩ := ht W f hf
    have := hM
    first
    | exact ⟨M, Module.finitePresentation_of_finite A M, e⟩
    | exact ⟨M, inferInstance, e⟩

private theorem commonStratification (s : Finset ℤ)
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (F : ℤ → Mod (constant (coefficientProEtaleModelTopology.{u, v} X) A))
    (hF : ∀ j ∈ s, IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A (F j)) :
    ∃ S : Stratification X, ∀ j ∈ s, ∀ a : Fin S.n,
      IsCoefficientModelLocallyConstantFinite _ A
        ((coefficientProEtaleFixedModulePullback (S.immersion a) A).obj
          ((coefficientModelFixedScalars _ A).obj (F j))) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Stratification.trivial X, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨S, hS⟩ := ih (fun k hk ↦ hF k (Finset.mem_insert_of_mem hk))
    obtain ⟨T, _, hT⟩ := (proEtale_noetherian_global_constructibility X A (F j)).mp
      (hF j (Finset.mem_insert_self j s))
    refine ⟨S.inter T, ?_⟩
    intro k hk a
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      change IsCoefficientModelLocallyConstantFinite _ A
        ((coefficientProEtaleFixedModulePullback
          (CategoryTheory.Limits.pullback.fst _ _ ≫ S.immersion _) A).obj _)
      rw [CategoryTheory.Limits.pullback.condition]
      exact ProEtale.coefficientProEtale_finite_comp
        (CategoryTheory.Limits.pullback.snd _ _) (T.immersion _) A _
        ((finiteModels_iff_presentation _ A _).mpr (hT _))
    · exact ProEtale.coefficientProEtale_finite_comp
        (CategoryTheory.Limits.pullback.fst _ _) (S.immersion _) A _ (hS k hk _)

/-- A finite constant tensor factor preserves constructibility degree by degree.
There is no lower bound or flatness assumption on the constant factor.
(Stacks, Tags 09BQ, 094H) -/
theorem coefficientConstructible_constantTensor (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (K : adicFiniteAmbient.{u, v} X A)
    (hK : ProEtale.coefficientBoundedConstructibleProEtale.{u, v} X A K)
    (M : ModuleCat.{max v (u + 1)} A) (hM : Module.Finite A M) (q : ℤ) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X A
      ((coefficientModelCohomology _ q).obj
        (coefficientConstantTensor.{u, v} X A K M)) := by
  classical
  obtain ⟨a, b, _, hb⟩ := hK.2
  let H := fun j : ℤ ↦ (coefficientModelCohomology _ j).obj K
  obtain ⟨S, hS⟩ := commonStratification.{u, v} (Finset.Icc a b) X A H (fun j _ ↦ hK.1 j)
  apply (proEtale_noetherian_global_constructibility X A _).mpr
  refine ⟨S, S.isConstructible_stratum, fun i ↦ ?_⟩
  apply (finiteModels_iff_presentation _ A _).mp
  apply coefficientConstantTensor_restricted_finite.{u, v} (S.immersion i) A K
    ⟨b, fun j hj ↦ hb j (Or.inr hj)⟩ ?_ M hM q
  intro j hj
  exact hS j (Finset.mem_Icc.mpr (by
    constructor
    · by_contra h
      exact hj (hb j (Or.inl (lt_of_not_ge h)))
    · by_contra h
      exact hj (hb j (Or.inr (lt_of_not_ge h))))) i

end AlgebraicGeometry.Scheme
