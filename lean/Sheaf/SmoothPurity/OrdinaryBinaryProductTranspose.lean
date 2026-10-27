/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.SmoothPurity.OrdinaryProductTransposeData

/-! # The binary ordinary-product transpose
Source: blueprint sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md, two-counit calculation
(blueprint: lem-pur-ordinary-binary-product-transpose). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting
variable (P : PurityFiniteSetting.{u})

/-- The actual symmetry/projection/exchange product transposes to the two pulled-back
counits on arbitrary unbounded fixed-scalar derived categories.
Source: blueprint relative Kunneth coherence proof, clauses (i)--(ii), and
lem-pur-ordinary-triple-product-transpose, proof steps 2--5
(blueprint: lem-pur-ordinary-binary-product-transpose).

Proof: transpose the inner projection after exchange. The projection definition
and tensor comparison naturality give the exchange transpose tensored with identity.
The exchange mate equation identifies its first factor with the pulled-back first
counit through the square's pullback-composition comparison. Transpose the outer
projection and its two signed swaps. Pullback preserves signed symmetry, so symmetry
naturality and its inverse law cancel the swaps, leaving identity tensored with the
second counit. Successive transposition through the specified direct-image compositor
is ordinaryDerivedCompositeTranspose. Tensor naturality and compatibility with pullback
composition now give exactly ordinaryBinaryEvaluation. The only inverses used are
canonical tensor and composition comparisons; exchange and projection need not be iso. -/
theorem ordinaryBinaryProductTranspose {W X Y B : Scheme.{u}}
    {r : W ⟶ X} {t : W ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : IsPullback r t f g) (K : P.ordinaryCategory X) (L : P.ordinaryCategory Y) :
    ((P.ordinaryAdj (t ≫ g)).homEquiv _ _).symm (P.ordinaryProduct sq K L) =
      P.ordinaryBinaryEvaluation sq ((P.ordinaryPush f).obj K)
        ((P.ordinaryPush g).obj L) K L
        ((P.ordinaryAdj f).counit.app K) ((P.ordinaryAdj g).counit.app L) := by sorry

end WeilConjectures.PurityFiniteSetting
