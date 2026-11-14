/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Section.SectionAffineOpenKillsCohomology
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroSectionPowerObstruction

/-! # Lifting a tensor power of a section across a square-zero immersion

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1) and the boundary
calculation following it.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Some positive tensor power of the given section lifts, after the tensor-power
and pullback identifications. The conclusion is equality of section morphisms;
it makes no assertion about nonvanishing loci or affineness upstairs.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1) and the following
boundary calculation. -/
theorem exists_section_power_lift_of_square_zero
    {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian Z] [CompactSpace Z]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (s : (((tensorPullback j).obj L).tensorPow n).val.presheaf.obj
      (Opposite.op ⊤)) (U : Z.Opens)
    (hU : (U : Set Z) = nonvanishingLocus (((tensorPullback j).obj L).tensorPow n) s)
    (hAffine : IsAffineOpen U) :
    ∃ k : ℕ, 0 < k ∧
      ∃ t : (L.tensorPow (n * k)).val.presheaf.obj (Opposite.op ⊤),
        ∃ e : (tensorPullback j).obj (L.tensorPow (n * k)) ≅
            (((tensorPullback j).obj L).tensorPow n).tensorPow k,
          homOfGlobalSection ((tensorPullback j).obj (L.tensorPow (n * k)))
              (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
                (L.tensorPow (n * k))).val.app (Opposite.op ⊤) t) ≫ e.hom =
            tensorPowSection (homOfGlobalSection
              (((tensorPullback j).obj L).tensorPow n) s) k := by
  classical
  have : ((tensorPullback j).obj L).IsInvertible :=
    ((invertible_pullback_tensor j).1 L).2
  let F := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
  obtain ⟨hF, xi, hlift⟩ := exists_square_zero_section_power_obstruction j L hI n s
  have : F.IsQuasicoherent := hF
  obtain ⟨e, he⟩ := exists_tensorPowSection_cohomology_eq_zero Z
    (((tensorPullback j).obj L).tensorPow n) s U hU hAffine F 1 (by decide) xi
  obtain ⟨t, a, ha⟩ := hlift e he
  exact ⟨e + 1, Nat.zero_lt_succ e, t, a, ha⟩

end AlgebraicGeometry.Scheme.Modules
