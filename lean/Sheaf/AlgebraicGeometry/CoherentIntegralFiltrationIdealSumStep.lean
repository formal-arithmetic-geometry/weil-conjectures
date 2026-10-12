/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian

/-! The split-sum induction step for coherent integral filtrations.
(blueprint: lem-weil-pbc-coherent-integral-filtration-ideal-sum-succ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Appending one summand to a coherent integral-ideal filtration.
(blueprint: lem-weil-pbc-coherent-integral-filtration-ideal-sum-succ)

Proof: finite pushforward coherence makes A = i_*I coherent. Write the pushforward
of the (r+1)-fold sum as B ⊕ A, where B is the pushforward of the r-fold sum;
sectionwise pushforward preserves finite sums because they are finite products.
Take the supplied chain of coherent subobjects of B, compose its inclusions with
the split monomorphism B → B ⊕ A, and then append the full subobject of B ⊕ A.
Monotonicity and the bottom endpoint are preserved. The old stages remain coherent
by their isomorphisms with the supplied stages, and the new full stage is coherent
by finite-sum closure. The old consecutive cokernels are unchanged up to isomorphism;
the final cokernel is A by the split-sum identities, with witness Z, i, I, hne, hI.
Transport the chain back along the finite-sum comparison. If the supplied chain has
length zero, B is zero and the same construction gives just the one quotient A.
Source: Stacks Project, Tag 01YF, final paragraph of `lemma-coherent-filter`.
-/
theorem coherentIntegralFiltration_ideal_sum_succ
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (r : ℕ) (I : Z.IdealSheafData) (hne : I ≠ ⊥)
    (hI : RingedSpace.IsCoherent Z.toRingedSpace I.toModules)
    (hprev : HasCoherentIntegralFiltration
      ((pushforward i).obj (∐ fun _ : Fin r => I.toModules))) :
    HasCoherentIntegralFiltration
      ((pushforward i).obj (∐ fun _ : Fin (r + 1) => I.toModules)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
