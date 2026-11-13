/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.CoherentKernelConditionRestriction
import WeilConjectures.AlgebraicGeometry.CoherentKernelConditionDescent
import WeilConjectures.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCore

/-! # Coherence of a module is local on an open covering

Source: Stacks Project, Modules, Definitions 01BV and 01B5; locality used in
Cohomology of Schemes, Lemma 0CYJ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Coherence of a module is preserved by restriction to opens and is local on an open cover:
(1) if `F` is coherent then `F|_W` is a coherent `𝒪_W`-module for every open `W`; (2) if every
`F|_{U i}` is coherent and the `U i` cover `X`, then `F` is coherent. Restriction is Mathlib's
`Scheme.Modules.restrictFunctor` along the open immersion `W.ι`, coherence the project's
`RingedSpace.IsCoherent` (pqf-def-coherent).
Source: Stacks Project, Modules, Definitions 01BV and 01B5; the locality is used in
Cohomology of Schemes, Lemma 0CYJ. -/
theorem coherent_module_local_on_open_cover
    (X : Scheme.{u}) (F : X.Modules) (I : Type u)
    (U : I → X.Opens)
    (hU : ⨆ i, U i = ⊤) :
    (RingedSpace.IsCoherent X.toRingedSpace F →
      ∀ (W : X.Opens),
        RingedSpace.IsCoherent W.toScheme.toRingedSpace
          ((Scheme.Modules.restrictFunctor W.ι).obj F)) ∧
      ((∀ (i : I),
          RingedSpace.IsCoherent (U i).toScheme.toRingedSpace
            ((Scheme.Modules.restrictFunctor (U i).ι).obj F)) →
        RingedSpace.IsCoherent X.toRingedSpace F) := by
  obtain ⟨hFT_restrict, hFT_cover⟩ :=
    coherent_module_finite_type_local_core X F I U hU
  constructor
  · intro hF W
    exact ⟨hFT_restrict hF W,
      coherent_kernel_condition_restriction X F hF.2 W⟩
  · intro hF
    exact ⟨hFT_cover hF,
      coherent_kernel_condition_descent X F I U hU (fun i ↦ (hF i).2)⟩

end AlgebraicGeometry
