/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Valuation.ValuationRing
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Vanishing of sections on the closed fibre of a valuation ring

Source: Stacks Project, More on Morphisms, Tag 0EX8,
Lemma `lemma-triviality-generic-fibre-valuation-ring`, closed-fibre section descent
(blueprint: lem-sc-valuation-closed-fibre-section-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A section vanishing on the closed fibre vanishes modulo a nonzero element of the
maximal ideal. Source: Stacks Project, Tag 0EX8, proof of
`lemma-triviality-generic-fibre-valuation-ring`.
(blueprint: lem-sc-valuation-closed-fibre-section-vanishing)

Proof:
1. Since the valuation ring is not a field, its maximal ideal contains a nonzero element.
   Nonzero elements of the maximal ideal, ordered by divisibility, give a filtered system
   of quotients with colimit the residue field. The corresponding base changes of `X`
   form an inverse system with affine transition maps and limit the closed fibre.
   Fix one stage and restrict `L` and `s` to it; further pullbacks are their restrictions.
2. Apply `lem-sc-valuation-limit-qcoh-section-descent` to this quasi-coherent module on
   the quasi-compact quasi-separated stages. Its eventual-zero clause gives a nonzero
   element of the maximal ideal at whose stage the section vanishes. -/
theorem exists_nonzero_maximalIdeal_section_eq_zero
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (hA : ¬ IsField A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (L : X.Modules) [L.IsInvertible] (s : L.val.obj (op ⊤))
    (hs : ((Classical.choose (exists_tensorPullbackAdjunction
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))))).unit.app L).val.app (op ⊤) s = 0) :
    ∃ π : A, π ≠ 0 ∧ π ∈ IsLocalRing.maximalIdeal A ∧
      ((Classical.choose (exists_tensorPullbackAdjunction
        (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {π}))))))).unit.app L).val.app (op ⊤) s = 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
