/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientFixedClosedUnitEpi
import WeilConjectures.AlgebraicGeometry.CoefficientOpenClosedKernel

/-! The open extension-by-zero comparison for the coefficient-sized closed-unit kernel. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale

/-- The kernel of the canonical closed unit is classical when the open restriction is.
Source: Stacks Project, Tag 09AH, lemma-ses-associated-to-open, and Tag 09AF,
lemma-jshriek-comparison. -/
theorem coefficientFixed_localization_kernel_comparison
    (A : Type (max v (u + 1))) [CommRing A]
    {X Z U : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (hj : (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} U) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} U)
      (Scheme.coefficientProEtaleModelTopology.{u, v} U)).essImage
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} j A).obj F))
    [HasKernel (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) ((coefficientFixedCanonicalAdj.{u, v} A i).unit.app F)] :
    (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).essImage
        (kernel (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
          (ModuleCat.{max v (u + 1)} A))
          ((coefficientFixedCanonicalAdj.{u, v} A i).unit.app F)) := by
  obtain ⟨G, ⟨e⟩⟩ := hj
  obtain ⟨k⟩ := coefficientOpenClosedKernelIso.{u, v} A i j hU F
  refine ⟨(coefficientOpenEtaleExtension.{u, v} A j).obj G, ⟨?_⟩⟩
  exact (coefficientOpenExtensionComparisonIso.{u, v} A j).app G ≪≫
    (coefficientOpenProEtaleExtension.{u, v} A j).mapIso e ≪≫ k

end AlgebraicGeometry.ProEtale
