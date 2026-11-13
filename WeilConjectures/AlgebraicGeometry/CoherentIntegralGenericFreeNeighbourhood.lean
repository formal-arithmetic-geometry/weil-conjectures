/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.CoherentStalkMapExtends
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleStalkFinite
import WeilConjectures.AlgebraicGeometry.FiniteFreeModuleStalkEquiv
import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! Generic coherent ideal lattices. Source: Stacks Project, Tag 01YE. -/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite generic basis extends to a finite free map on an open neighbourhood (Stacks, Tag 01YE).
-/
theorem exists_generic_free_neighbourhood (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules)
    (hG : RingedSpace.IsCoherent Z.toRingedSpace G) :
    ∃ (r : ℕ) (U : Z.Opens) (hx : genericPoint Z ∈ U)
      (φ : (restrictFunctor U.ι).obj
          (SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r))) ⟶
        (restrictFunctor U.ι).obj G),
      IsIso ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
        (⟨genericPoint Z, hx⟩ : U.toScheme)).map φ) := by
  classical
  have : G.IsFiniteType := hG.1
  let ξ := genericPoint Z
  let K := Z.presheaf.stalk ξ
  let M := (RingedSpace.moduleStalkFunctor Z.toRingedSpace ξ).obj G
  have : Module.Finite K M := finite_moduleStalk_of_isFiniteType Z G ξ
  let b := Module.finBasis K M
  let r := Module.finrank K M
  let E : Z.Modules := SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r))
  obtain ⟨e⟩ := exists_finite_free_moduleStalk_linearEquiv Z (ULift.{w} (Fin r)) ξ
  let bg := b.reindex Equiv.ulift.symm
  let ψ := (e.trans bg.equivFun.symm).toModuleIso
  let P := SheafOfModules.presentationOfIsCokernelFree
    (0 : SheafOfModules.free (PEmpty.{w + 1}) ⟶ E)
    (𝟙 E) (by simp) (Limits.CokernelCofork.IsColimit.ofId _ rfl)
  have : P.IsFinite := ⟨⟨inferInstanceAs (Finite (ULift.{w} (Fin r)))⟩,
    ⟨inferInstanceAs (Finite (PEmpty.{w + 1}))⟩⟩
  have : E.IsFinitePresentation := P.isFinitePresentation
  have hE : RingedSpace.IsCoherent Z.toRingedSpace E := by
    apply (isCoherent_iff_isQuasicoherent_and_isFiniteType Z E).2
    constructor <;> infer_instance
  obtain ⟨U, hx, φ, hφ⟩ :=
    exists_open_hom_of_coherent_stalk_map G E hG hE ξ ψ.hom
  refine ⟨r, U, hx, φ, ?_⟩
  apply (ConcreteCategory.isIso_iff_bijective _).2
  let y : U.toScheme := ⟨ξ, hx⟩
  let s := restrictStalkNatIso U.ι y
  let f := (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y).map φ
  have heq : (fun m ↦ ConcreteCategory.hom (s.hom.app G)
      (f (ConcreteCategory.hom (s.inv.app E) m))) = ψ.hom := by
    funext m
    exact (hφ m).symm
  have hb : Function.Bijective (fun m ↦ ConcreteCategory.hom (s.hom.app G)
      (f (ConcreteCategory.hom (s.inv.app E) m))) := by
    rw [heq]
    exact ConcreteCategory.bijective_of_isIso ψ.hom
  exact ((ConcreteCategory.bijective_of_isIso (s.hom.app G)).of_comp_iff' _).mp
    (((Function.Bijective.of_comp_iff _
      (ConcreteCategory.bijective_of_isIso (s.inv.app E))).mp hb))

end AlgebraicGeometry.Scheme.Modules
