/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons

/-! # Finite coefficient pullback coherence in fixed-scalar coordinates

Source: the finite-reduction proof Step 2, expanded presentation-reduction Step 7;
Stacks Project, sites-cohomology.tex, Tag 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The recorded coefficient pullback mate respects the binary derived tensor maps.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2; expanded parent proof Step 7;
Stacks 07A4 (blueprint: lem-pur-finite-tensor-pullback-tensor-reduction).
Proof: resolve K and L by flat-term K-flat cochains. Geometric ringed pullback and
coefficient change preserve these representatives. The coefficient-extension tensor
square of cochainPullbackTensorCoherence commutes: on pure sections both routes
associate the scalar with the pulled-back factors, with the same scalar-first
binary map. The scalar unit sends x to x tensor 1, so adjoint transposition of this
section map is exactly the recorded coefficient pullback mate, not an independently
chosen isomorphism. The normalized finiteTensorCore is the descent of the same
binary map. The fixed pullback tensor is the descent of the inverse-image tensor
comparison. Descend the cochain square through the localization equivalence, then
transport it through the scalar and pullback realization isomorphisms in
finiteTensorPullbackComparison. Their units and counits cancel by the triangle
identities. Faithfulness of the realization equivalence and naturality along the
representative isomorphisms give the displayed equality for arbitrary K and L.
This argument uses K-flatness, not flatness of the coefficient quotient; it also
applies to identity morphisms, empty schemes and equal coefficient levels. -/
theorem finiteTensorPullbackTensorReduction (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∀ K L,
      (P.finiteTensorReduction m hm hmn X).map
          (P.finiteTensorPullbackTensor f K L).hom ≫
        ((P.finiteTensorCore m hm hmn X).μIso
          ((P.smoothPurityPullback f).obj K) ((P.smoothPurityPullback f).obj L)).inv ≫
        ((P.finiteTensorPullbackComparison m hm hmn f K).hom ⊗ₘ
          (P.finiteTensorPullbackComparison m hm hmn f L).hom) =
      (P.finiteTensorPullbackComparison m hm hmn f (K ⊗ L)).hom ≫
        ((P.finiteReductionSetting m hm).smoothPurityPullback f).map
          ((P.finiteTensorCore m hm hmn Y).μIso K L).inv ≫
        ((P.finiteReductionSetting m hm).finiteTensorPullbackTensor f
          ((P.finiteTensorReduction m hm hmn Y).obj K)
          ((P.finiteTensorReduction m hm hmn Y).obj L)).hom := by sorry

end WeilConjectures.PurityFiniteSetting
