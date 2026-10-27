module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! # Canonical biduality for a dualizable object with right internal Homs

Source: Stacks Project, `categories.tex`, Tags 0FFP, 0FFQ and 0FFR, together with
Mathlib's braided exchange of an exact pairing
(blueprint: lem-trf-dualizable-braided-canonical-bidual).

The internal Hom functors and their adjunctions are supplied explicitly, with
`tensorRight L` as left adjoint. This retains the specified evaluation and transpose.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory

open MonoidalCategory

/-- The transpose of evaluation after the braiding is invertible for an object with a dual.
Here `H L` is the specified right internal Hom `[L,-]`, and its evaluation is the counit
of `adj L`. The braiding is arbitrary, with no symmetry assumption.

Source: Stacks Project, `categories.tex`, Tags 0FFP (definition-dual), 0FFQ
(lemma-left-dual), and 0FFR (remark-left-dual-adjoint), with the braided exchange of an
exact pairing (blueprint: lem-trf-dualizable-braided-canonical-bidual).

Proof:
1. Write `D = (H X).obj (𝟙_ C)` and `v = (adj X).counit.app (𝟙_ C)`. The dual-pair
   formulas of Tag 0FFQ identify maps `K → Y` with maps `K ⊗ X → 𝟙_ C`: compose with
   the evaluation to go forward, and tensor with the coevaluation and contract to go
   backward, inserting the associators and unitors. The two triangle identities give
   the two inverse identities (def-sfb-monoidal-category).
2. Transpose the pairing's evaluation to obtain `t : Y → D`. The preceding inverse
   formula applied to `v` gives its inverse `s : D → Y`; transpose uniqueness verifies
   `t` and `s` are inverse. Transport the exact pairing along this isomorphism
   (lem-trf-exact-pairing-iso-transport, Mathlib's `exactPairingCongr`), obtaining
   coevaluation `a : 𝟙_ C → X ⊗ D` and evaluation exactly `v`.
3. Swap this pairing using `BraidedCategory.exactPairing_swap`
   (lem-trf-exact-pairing-braided-swap). The new coevaluation is
   `c = a ≫ (β_ D X).inv`, and the new evaluation is `w = (β_ X D).hom ≫ v`.
   Both triangle identities hold without identifying a braiding with an inverse.
4. Put `E = (H D).obj (𝟙_ C)` and `u = (adj D).counit.app (𝟙_ C)`. The displayed
   transpose `b : X → E` satisfies `(b ▷ D) ≫ u = w`. Define `k : E → X` by
   tensoring with `c` and contracting with `u`, using associators and unitors.
   The `X` triangle gives `b ≫ k = 𝟙 X`. The `D` triangle and bifunctoriality give
   `(k ▷ D) ≫ w = u`; transpose uniqueness then gives `k ≫ b = 𝟙 E`.
   Thus the specified transpose has a two-sided inverse.
-/
theorem isIso_braided_rightClosed_bidual
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : C → C ⥤ C) (adj : ∀ L : C, tensorRight L ⊣ H L)
    (X Y : C) [ExactPairing X Y] :
    IsIso
      ((adj ((H X).obj (𝟙_ C))).homEquiv X (𝟙_ C)
        ((β_ X ((H X).obj (𝟙_ C))).hom ≫ (adj X).counit.app (𝟙_ C))) := by
  sorry

end CategoryTheory
