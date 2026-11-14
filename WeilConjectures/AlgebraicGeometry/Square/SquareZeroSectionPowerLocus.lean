/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroSectionPowerLift
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement

/-! # Lifting the nonvanishing open of a section across a square-zero immersion

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, square-zero case, from the tensor exact
sequence through the lifting of a power of a section.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- An affine nonvanishing open downstairs is the inverse image of the nonvanishing
locus of a section of a positive multiple of the original tensor degree upstairs.
This asserts neither ampleness nor affineness of the open upstairs.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1) and the next
paragraph, ending with the lift of a power of the section. -/
theorem exists_section_power_locus_of_square_zero
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
        ∀ z : Z, j z ∈ nonvanishingLocus (L.tensorPow (n * k)) t ↔ z ∈ U := by
  classical
  have : ((tensorPullback j).obj L).IsInvertible :=
    ((invertible_pullback_tensor j).1 L).2
  obtain ⟨k, hk, t, e, he⟩ := exists_section_power_lift_of_square_zero
    j L hI n s U hU hAffine
  let res := (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
    (L.tensorPow (n * k))).val.app (Opposite.op ⊤) t)
  have hz := Hom.zeroLocus_eq_of_arrowIso
    (homOfGlobalSection ((tensorPullback j).obj (L.tensorPow (n * k))) res)
    (tensorPowSection (homOfGlobalSection (((tensorPullback j).obj L).tensorPow n) s) k)
    (Arrow.isoMk (Iso.refl _) e (by
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
      exact he.symm))
  have hloc : nonvanishingLocus ((tensorPullback j).obj (L.tensorPow (n * k))) res =
      nonvanishingLocus (((tensorPullback j).obj L).tensorPow n) s := by
    have : ((tensorPullback j).obj (L.tensorPow (n * k))).IsInvertible :=
      ((invertible_pullback_tensor j).1 (L.tensorPow (n * k))).2
    rw [nonvanishingLocus_eq_compl_support_zeroLocus,
      nonvanishingLocus_eq_compl_support_zeroLocus, hz,
      compl_support_zeroLocus_tensorPowSection _ _ hk]
  refine ⟨k, hk, t, fun z ↦ ?_⟩
  exact (nonvanishing_tensorPullback j (L.tensorPow (n * k)) t z).symm.trans
    ((Set.ext_iff.mp hloc z).trans (Set.ext_iff.mp hU z).symm)

end AlgebraicGeometry.Scheme.Modules
