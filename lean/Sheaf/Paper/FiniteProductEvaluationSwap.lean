/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.FiniteProperProductMaps

/-! # Swap compatibility for arbitrary tensor evaluation maps

Source: Stacks Tags 0E48 and 07A4; the symmetry-naturalness calculation in the
proper-product paragraph of the current relative Kunneth coherence blueprint.
(blueprint: lem-pur-finite-product-evaluation-swap).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteProperProduct

/-- Swapping two arbitrary evaluation maps commutes with the canonical pullback
and signed tensor comparisons. No exchange, projection, direct image or adjunction
counit occurs in this assertion.
Source: Stacks Tags 0E48 and 07A4; proper product symmetry calculation.
(blueprint: lem-pur-finite-product-evaluation-swap).

Proof: expand pairEvaluation and swapTensor. Naturality of the canonical pullback
monoidal comparison moves the tensor of the two evaluation maps past that
comparison. Pullback-composition associativity identifies the two occurrences of
each projection using the equations for pullbackSymmetry. The monoidal composition
law combines the successive tensor comparisons into that for the composite.
The signed-braiding compatibility of that comparison moves the input symmetry
through pullback. Naturality of the signed symmetry moves the two arbitrary
maps through the output symmetry. Finally involutivity cancels the two
symmetries. This proves equality for arbitrary evaluation arrows, including zero
maps, identity maps and arbitrary unbounded complexes, retaining Koszul signs. -/
theorem finiteProductEvaluationSwap (P : PurityFiniteSetting.{u})
    {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sB : B ⟶ Spec (.of P.field.k)) (sY : Y ⟶ Spec (.of P.field.k))
    (sZ : Z ⟶ Spec (.of P.field.k))
    (F G : D P B) (H : D P Y) (J : D P Z)
    (e : (pull P a).obj F ⟶ H) (d : (pull P b).obj G ⟶ J) :
    (pull P (pullback.snd a b ≫ b)).map (sigma P B F G).hom ≫
        (swapPull P a b).hom.app ((tensor P B).obj (G, F)) ≫
        (pull P (pullbackSymmetry a b).hom).map
          (pairEvaluation P b a sB sY G F J H d e) ≫
        swapTensor P a b sY sZ H J =
      pairEvaluation P a b sB sZ F G H J e d := by
  sorry

end WeilConjectures.FiniteProperProduct
