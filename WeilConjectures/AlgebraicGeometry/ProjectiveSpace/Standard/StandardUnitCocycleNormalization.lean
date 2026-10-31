/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.StandardUnitCocycleOffDiagonal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.StandardUnitCocycleDiagonal

/-!
# Normalizing unit cocycles on the standard projective-space cover

Source: Stacks Project, divisors.tex, Tag 0BXJ, lemma-Pic-projective-space-UFD.
(blueprint: lem-sfb-projective-standard-unit-cocycle-normalization)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- A cocycle of units on the standard cover, with at least three homogeneous
coordinates, differs from a standard integer transition cocycle by chart units.
This is a statement about functions, with no module sheaf or gluing conclusion.

Source: Stacks Project, divisors.tex, Tag 0BXJ, proof of
lemma-Pic-projective-space-UFD, the double- and triple-overlap calculations.
(blueprint: lem-sfb-projective-standard-unit-cocycle-normalization)

Proof: For distinct i,j identify the overlap ring with the Laurent polynomial
ring k[t,t^-1,z], with t=T_i/T_j. Since degrees in each z add for products over
a domain, a unit has degree zero in all the z. The greatest and least exponents
of a Laurent polynomial add under multiplication. A unit therefore has just one
exponent and is c*t^e, with c in k^*. This expression is unique. On a triple
intersection with distinct indices i,j,k, the ratios T_i/T_j and T_j/T_k are
algebraically independent Laurent variables. Substitution in the cocycle equation
and comparison of their exponents gives e_ij=e_jk=e_ik, and comparison of constants
gives c_ij*c_jk=c_ik. Reversing a pair gives the same exponent; the graph of pairs
is connected by triples when there are at least three indices. Thus there is a
single integer d. The diagonal equations give t_ii=1 and c_ii=1. Fix an index b.
The scalar cocycle is the boundary c_ij=c_ib/c_jb. Choose a_i=c_ib^-1, regarded
as a constant chart unit. Then a_i*t_ij=(T_i/T_j)^d*a_j on every overlap, also
when indices coincide. All arguments use only that k is a field. -/
theorem exists_standardUnitCocycle_normalization (k : Type u) [Field k]
    (r : ℕ) (hr : 3 ≤ r)
    (t : ∀ i j : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
        standardOpen _ (Spec (.of k)) i ⊓ standardOpen _ (Spec (.of k)) j)ˣ)
    (ht : ∀ (i j l : ULift.{u} (Fin r))
      (W : ℙ(ULift.{u} (Fin r); Spec (.of k)).Opens)
      (hi : W ≤ standardOpen _ (Spec (.of k)) i)
      (hj : W ≤ standardOpen _ (Spec (.of k)) j)
      (hl : W ≤ standardOpen _ (Spec (.of k)) l),
      (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hi hj)).op (t i j).val *
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hj hl)).op (t j l).val =
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hi hl)).op (t i l).val) :
    ∃ d : ℤ, ∃ a : ∀ i : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), standardOpen _ (Spec (.of k)) i)ˣ,
      ∀ i j : ULift.{u} (Fin r),
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
            (homOfLE inf_le_left).op (a i).val * (t i j).val =
          (transitionUnit _ (Spec (.of k)) d i j).val *
            (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
              (homOfLE inf_le_right).op (a j).val := by
  obtain ⟨d, a, hoff⟩ := exists_standardUnitCocycle_normalization_offDiagonal k r hr t ht
  have hdiag := standardUnitCocycle_diagonal_normalization k r hr t ht d a hoff
  refine ⟨d, a, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    exact hdiag i
  · exact hoff i j hij

end AlgebraicGeometry.ProjectiveSpace
