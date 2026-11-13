/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.ClosedStructureAmbientIdealExtension
import WeilConjectures.AlgebraicGeometry.ClosedStructureIdealProductIso
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Clearing denominators for a local map from a closed structure module

## References

* [Stacks, Tags 01YB, 01YE and 01QY]
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- A local map from a closed structure module extends after restricting its source
by a nonzero ideal on the integral closed subscheme. No injectivity is assumed or
asserted. Agreement holds on the entire given open, not just on the generic stalk. -/
theorem local_closed_ideal_map_extension
    {X W : Scheme.{u}} [IsNoetherian X]
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (U : X.Opens) (hx : i.base (genericPoint W) ∈ U)
    (φ : (restrictFunctor U.ι).obj
        ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) ⟶
      (restrictFunctor U.ι).obj G) :
    ∃ (J : W.IdealSheafData), J ≠ ⊥ ∧
      ∃ (α : (pushforward i).obj J.toModules ⟶ G),
        (restrictFunctor U.ι).map α =
          (restrictFunctor U.ι).map ((pushforward i).map J.toModulesι) ≫ φ := by
  let I : X.IdealSheafData := IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.2.isClosed_compl⟩
  have hI : (I.support : Set X) = (U : Set X)ᶜ := by
    simp [I]
  obtain ⟨n, χ, hχ⟩ := closed_structure_ambient_ideal_extension i I G hG U hI φ
  let J : W.IdealSheafData := (I ^ n).comap i
  have hJ : J ≠ ⊥ := by
    intro hzero
    have hmem : genericPoint W ∈ (J.support : Set W) := by
      rw [hzero, IdealSheafData.support_bot]
      trivial
    have hmem' : i.base (genericPoint W) ∈ ((I ^ n).support : Set X) := by
      change genericPoint W ∈ (((I ^ n).comap i).support : Set W) at hmem
      rw [IdealSheafData.support_comap] at hmem
      exact hmem
    have hmemI : i.base (genericPoint W) ∈ (I.support : Set X) :=
      IdealSheafData.support_pow_le n hmem'
    rw [hI] at hmemI
    exact hmemI hx
  obtain ⟨e, he⟩ := closed_structure_ideal_product_iso i (I ^ n)
  refine ⟨J, hJ, e.hom ≫ χ, ?_⟩
  rw [Functor.map_comp, hχ, ← Category.assoc, ← Functor.map_comp, he]


end AlgebraicGeometry.Scheme.Modules
