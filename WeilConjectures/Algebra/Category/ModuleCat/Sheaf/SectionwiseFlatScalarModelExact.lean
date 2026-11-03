/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
public import Mathlib.RingTheory.Flat.Basic
import all WeilConjectures.Algebra.Homology.IndFiniteFree.IndFiniteFreeScalarModel
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Exact scalar extension from sectionwise flatness

Source: the finite-free argument in paragraph 1 of
`lem-coef-integral-finite-extension.proof.md`, Stacks Tags 03EK and 08FC.
(blueprint: lem-sf-sectionwise-flat-scalar-model-exact)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- Sectionwise flat coefficient maps have exact ordinary scalar extension.
Source: blueprint `lem-coef-integral-finite-extension.proof.md`, finite-free argument;
Stacks Tags 03EK and 08FC (blueprint: lem-sf-sectionwise-flat-scalar-model-exact).
Proof: any finite relation in the restricted target coefficient module becomes a
trivial relation after restriction to any site object, by sectionwise flatness.
The top sieve therefore witnesses the local equational criterion. The comparison
between sheaf tensor and ordinary extension followed by restriction identifies the
latter with tensor by this flat coefficient module. Restriction reflects finite
limits and extension is a left adjoint, proving the two exactness clauses. -/
theorem scalarModel_exact_of_sectionwise_flat
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) (A : SystemScalarModel φ)
    (hflat : ∀ U : Cᵒᵖ,
      letI : Module (R.obj.obj U) (S.obj.obj U) :=
        Module.compHom _ (φ.hom.app U).hom
      Module.Flat (R.obj.obj U) (S.obj.obj U)) :
    PreservesFiniteLimits A.model.E ∧ PreservesFiniteColimits A.model.E := by
  let M := (IndFiniteFree.algebraModules R).obj (Under.mk φ)
  have hsite : IsFlatOnSite (R := R) M := by
    apply isFlatOnSite_of_local_equationalCriterion R M
    intro U n a s hs
    refine ⟨⊤, J.top_mem U, ?_⟩
    intro V f _hf
    let : Module.Flat (R.obj.obj (op V)) (M.val.obj (op V)) := hflat (op V)
    apply Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    calc
      ∑ i, R.obj.map f.op (a i) • M.val.map f.op (s i) =
          ∑ i, M.val.map f.op (a i • s i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (M.val.map_smul f.op (a i) (s i)).symm
      _ = M.val.map f.op (∑ i, a i • s i) := (map_sum _ _ _).symm
      _ = 0 := by rw [hs, map_zero]
  have hright : PreservesFiniteLimits (tensorRight M) := by
    have : PreservesFiniteLimits (siteSheafTensorRight M) := hsite.1
    exact preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R M)
  have : PreservesFiniteLimits (tensorLeft M) := by
    have := hright
    exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm
  have : PreservesFiniteLimits (A.model.E ⋙ IndFiniteFree.restriction φ) :=
    preservesFiniteLimits_of_natIso (IndFiniteFree.ordinaryComparison A.model)
  have : (IndFiniteFree.restriction φ).ReflectsIsomorphisms := by
    have : (IndFiniteFree.restriction φ ⋙ toSheaf
        (derivedChangeRingIndependentCoefficients J R)).ReflectsIsomorphisms :=
      inferInstanceAs ((toSheaf
        (derivedChangeRingIndependentCoefficients J S)).ReflectsIsomorphisms)
    exact reflectsIsomorphisms_of_comp _ (toSheaf _)
  have : PreservesColimits A.model.E := A.ordinaryAdj.leftAdjoint_preservesColimits
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves A.model.E
    (IndFiniteFree.restriction φ), inferInstance⟩

end SheafOfModules
