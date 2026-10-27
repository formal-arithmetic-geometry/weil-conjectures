/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import WeilConjectures.WeilSheaf.Dual

/-! # Equivariant balanced tensor restriction

Source: Stacks 03EL, 0E8I and the native open tensor argument, step 2.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

/-- The actual balanced restriction/tensor comparison lifts to Weil sheaves.

Source: Stacks Project, sites-modules.tex, Tags 03EL and 0E8I; step 2 of
lem-sf-native-open-sheaf-tensor-existence.
(blueprint: lem-sf-native-open-restriction-tensor).

Proof: the ordinary coefficient pullback is the map on locally finite functions
induced by precomposition. Its balanced tensor comparison sends a pulled-back
pure tensor to the tensor of its two pullbacks. Apply this formula before and
after Frobenius. Both maps pull back the same two sections and then apply their
Weil structures, since j is defined over the finite field. The equality descends
through the balanced quotient and sheafification. Lift this ordinary comparison
and its inverse to the category of invertible Frobenius algebras. The inverse
identities and naturality follow by faithful forgetting from the ordinary ones.
This proves the stated underlying-map normalization as well. The construction
works on the empty open, the identity open and zero inputs without alteration. -/
theorem native_open_restriction_tensor :
    ∃ rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
        tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M),
      ∀ M N, HEq ((rho M N).hom.hom.f)
        ((ProEtale.adicUpperStarTensorLeftIso l
          (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
