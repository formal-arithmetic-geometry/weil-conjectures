/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModels
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Mathlib.RingTheory.Noetherian.Basic

/-! # Finitely presented local constant models on the pro-etale site

Source: Stacks Project, Tags 09AJ and 093U.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Finitely presented constant local models satisfy the local weak Serre clauses.
Source: Stacks Project, Tag 093U (3), lemma-kernel-finite-locally-constant.
(blueprint: lem-sfb-proetale-fp-local-models-serre).

Proof: use the equivalent AsSmall model of the pro-etale site. Forgetting commutativity
commutes with constant-ring sheafification, and restriction of scalars along the resulting
ring isomorphism is an exact equivalence. The module sheafification universal property
identifies constants and their localized restrictions in these two presentations.
Over a Noetherian ring finite presentation is equivalent to finite generation. Therefore
the generic finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions theorem
applies. Transport its kernel, cokernel, and extension conclusions through the exact
coefficient and site equivalences, retaining the same finite module values and converting
them back to finite presentations. Empty objects cause no exception. -/
theorem proEtale_fp_localModels_serre (X : Scheme.{u}) (R : Type u)
    [CommRing R] [IsNoetherianRing R] :
    (∀ (F G : proEtaleRingModules X (proEtaleConstantRing X R)) (f : F ⟶ G),
      IsFinitelyPresentedLocallyConstantProEtaleModule F →
      IsFinitelyPresentedLocallyConstantProEtaleModule G →
      IsFinitelyPresentedLocallyConstantProEtaleModule (kernel f) ∧
        IsFinitelyPresentedLocallyConstantProEtaleModule (cokernel f)) ∧
    (∀ S : ShortComplex (proEtaleRingModules X (proEtaleConstantRing X R)),
      S.ShortExact → IsFinitelyPresentedLocallyConstantProEtaleModule S.X₁ →
      IsFinitelyPresentedLocallyConstantProEtaleModule S.X₃ →
      IsFinitelyPresentedLocallyConstantProEtaleModule S.X₂) := by
  let : IsNoetherianRing (ULift.{u + 1, u} R) :=
    isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
  let E := proEtaleFPModelEncoding X R
  have : E.functor.IsEquivalence := E.isEquivalence_functor
  have h := SheafOfModules.finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions
    (proEtaleModelTopology X) (ULift.{u + 1, u} R)
  have trans {F G : ringedSiteModules.{u + 1}
      ((constantSheaf (proEtaleModelTopology X) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} R)))} (e : F ≅ G)
      (hF : SheafOfModules.IsFiniteTypeLocallyConstant (proEtaleModelTopology X)
        (ULift.{u + 1, u} R) F) :
      SheafOfModules.IsFiniteTypeLocallyConstant (proEtaleModelTopology X)
        (ULift.{u + 1, u} R) G := by
    intro V
    obtain ⟨T, hT, ht⟩ := hF V
    refine ⟨T, hT, fun W f hf ↦ ?_⟩
    obtain ⟨M, hM, ⟨i⟩⟩ := ht W f hf
    exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ W).mapIso e.symm ≪≫ i⟩⟩
  constructor
  · intro F G f hF hG
    obtain ⟨hK, hC⟩ := h.1 _ _ (E.functor.map f)
      ((proEtale_fp_localModels_comparison X R F).mp hF)
      ((proEtale_fp_localModels_comparison X R G).mp hG)
    exact ⟨(proEtale_fp_localModels_comparison X R _).mpr
        (trans (PreservesKernel.iso E.functor f).symm hK),
      (proEtale_fp_localModels_comparison X R _).mpr
        (trans (PreservesCokernel.iso E.functor f).symm hC)⟩
  · intro S hS h₁ h₃
    apply (proEtale_fp_localModels_comparison X R _).mpr
    exact h.2 (S.map E.functor) (hS.map_of_exact E.functor)
      ((proEtale_fp_localModels_comparison X R _).mp h₁)
      ((proEtale_fp_localModels_comparison X R _).mp h₃)

end AlgebraicGeometry.Scheme
