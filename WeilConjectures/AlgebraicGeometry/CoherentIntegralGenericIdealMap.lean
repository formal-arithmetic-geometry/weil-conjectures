/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentStalkMapExtends
import WeilConjectures.AlgebraicGeometry.CoherentLocalIsomorphism
import WeilConjectures.AlgebraicGeometry.CoherentHomsOverOpen
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericIdealConstruction
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericIdealMono

/-! # An ideal-sum lattice in a coherent module on an integral scheme

Stacks Project, Tag 01YE.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on an integral Noetherian scheme admits a coherent ideal-sum
injection with invertible generic stalk.
(Stacks, Tag 01YE). -/
theorem coherent_integral_generic_ideal_map (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules) (hG : RingedSpace.IsCoherent Z.toRingedSpace G) :
    ∃ (r : ℕ) (I : Z.IdealSheafData),
      RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
      RingedSpace.IsCoherent Z.toRingedSpace (∐ fun _ : Fin r => I.toModules) ∧
      ∃ (χ : (∐ fun _ : Fin r => I.toModules) ⟶ G), Mono χ ∧
        IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).map χ)
    := by
  obtain ⟨r, I, hI, hSum, χ, hχ⟩ :=
    coherent_integral_generic_ideal_construction Z G hG
  have hmono := mono_of_coherent_ideal_sum_generic_iso Z G hG r I χ hI hSum hχ
  exact ⟨r, I, hI, hSum, χ, hmono, hχ⟩

end AlgebraicGeometry.Scheme.Modules
