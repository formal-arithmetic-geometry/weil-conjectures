/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.AlgebraicGeometry.Square.SquareZeroSectionPowerLiftingCriterion
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Square-zero section-power obstruction

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u

/-- A section has a quasi-coherent degree-one obstruction on the closed subscheme.
If a tensor power of the section kills it, the next power lifts. No affine-open
hypothesis is needed to construct the obstruction or establish this implication.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1), and Cohomology,
Lemma 0B8S. -/
theorem exists_square_zero_section_power_obstruction
    {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (s : (((tensorPullback j).obj L).tensorPow n).val.presheaf.obj
      (Opposite.op ⊤)) :
    let F := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    F.IsQuasicoherent ∧ ∃ (xi : (RingedSpace.moduleCohomology Z.toRingedSpace 1).obj F),
      ∀ e : ℕ, (RingedSpace.moduleCohomology Z.toRingedSpace 1).map
        ((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection
          (((tensorPullback j).obj L).tensorPow n) s) e) xi = 0 →
      ∃ t : (L.tensorPow (n * (e + 1))).val.presheaf.obj (Opposite.op ⊤),
        ∃ a : (tensorPullback j).obj (L.tensorPow (n * (e + 1))) ≅
            (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1),
          homOfGlobalSection ((tensorPullback j).obj (L.tensorPow (n * (e + 1))))
              (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
                (L.tensorPow (n * (e + 1)))).val.app (Opposite.op ⊤) t) ≫ a.hom =
            tensorPowSection (homOfGlobalSection
              (((tensorPullback j).obj L).tensorPow n) s) (e + 1) := by
  dsimp only
  constructor
  · have := SheafOfModules.isQuasicoherent_unit (R := j.ker.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        ((SheafOfModules.pushforward j.ker.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit j.ker.subscheme.ringCatSheaf)) :=
      isQuasicoherent_pushforward_of_isClosedImmersion j.ker.subschemeι _
    have : j.ker.toModules.IsQuasicoherent :=
      isQuasicoherent_kernel j.ker.toPushforwardSubscheme
    have : (j.ker.toModules ⊗ L.tensorPow n).IsQuasicoherent :=
      isQuasicoherent_tensorObj _ _
    let a : tensorPullback j ≅ pullback j :=
      (Classical.choose (exists_tensorPullbackAdjunction j)).leftAdjointUniq
        (pullbackPushforwardAdjunction j)
    exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      (a.app _).symm (inferInstance : ((pullback j).obj _).IsQuasicoherent)
  · exact square_zero_section_power_obstruction_core j L hI n s

end AlgebraicGeometry.Scheme.Modules
