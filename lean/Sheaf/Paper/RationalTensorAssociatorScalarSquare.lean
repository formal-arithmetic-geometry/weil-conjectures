module

public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! # Scalar coherence and naturality of the prescribed rational tensor associator

Source: literature/stacks-project/sites-cohomology.tex, Tag 07A4, label
lemma-pullback-tensor-product; normalized completed/rational associator compatibility
(blueprint: lem-pur-rational-tensor-associator-scalar-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures

/-- The prescribed rational tensor associator is natural and commutes with the
specified scalar extension tensor comparison.

Source: literature/stacks-project/sites-cohomology.tex, Tag 07A4, label
lemma-pullback-tensor-product; the naturality clause is the arbitrary-arrow
naturality equation, and the scalar clause is the two composites obtained from
`rationalTensorScalarComparison` (blueprint: lem-pur-rational-tensor-associator-scalar-square).

Proof. Step 1 (integral objects). Choose the normalized primitive scalar model `S_Y`
and normalized Roos models from the ambient comparison-system family, and the tensor
model realizations `T_E, T_L` of the stage3 tensor-model normalization. The
reduction-intertwining lemma makes `γ` the invertible `scalarReduction` comparison of
`S_Y`. The stage3 scalar/tensor limit-square identifies the completed scalar/tensor
comparison with the two `scalarReduction` maps and `derivedSigma`. Apply coherent
reduction, use counit naturality and the derived-limit comparison of the
scalar-extension tower, and cancel `γ`, `γ ⊗ (γ ⊗ γ)` and the tensor reduction
comparison `r`. The system-associator lemma replaces the nested `derivedSigma`
composites by the `systemClosed.monoidal` associator, so both coherent reductions over
`𝒪_L` agree. Fully faithful coherent reduction reflects this, and the uniqueness
defining `pullbackTensorIntegralAssociator` gives the integral square
`B(α^int,E) ; B^⊗,r = B^⊗,l ; α^int,L`. The integral naturality lemma gives
integral naturality for arbitrary derived morphisms.
Step 2 (localization). The rational associator and `b` are the localizations of the
integral associator and of `integralTensorScalarComparison`; raw rationalization
preserves composition, so localizing Step 1 gives both equations on integral arrows.
Step 3 (all rational arrows). A rational morphism is a finite sum of pure integral
morphisms tensored with field scalars; the additive and balanced pure-tensor formulas
of the rational operations and of `sfRationalScalarExtension` extend both equations to
arbitrary `X, Y, Z` and arrows. This includes `E = L` and ramified extensions; no
finite-Tor or finite-type hypothesis is used.
-/
theorem rationalTensorAssociator_scalar_square
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    (∀ {K K' M M' N N' : sfRationalConstructibleCategory l E W}
      (f : K ⟶ K') (g : M ⟶ M') (h : N ⟶ N'),
      (rationalDerivedTensor l E W).map
          (Prod.mkHom ((rationalDerivedTensor l E W).map (Prod.mkHom f g)) h) ≫
          (pullbackTensorRationalAssociator l E W K' M' N').hom =
        (pullbackTensorRationalAssociator l E W K M N).hom ≫
          (rationalDerivedTensor l E W).map
            (Prod.mkHom f ((rationalDerivedTensor l E W).map (Prod.mkHom g h)))) ∧
    (∀ (X Y Z : sfRationalConstructibleCategory l E W),
      (sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
          (pullbackTensorRationalAssociator l E W X Y Z).hom ≫
        (rationalTensorScalarComparison l E L ι W).hom.app
          (X, (rationalDerivedTensor l E W).obj (Y, Z)) ≫
        (rationalDerivedTensor l L W).map
          (Prod.mkHom (𝟙 _) ((rationalTensorScalarComparison l E L ι W).hom.app
            (Y, Z))) =
      (rationalTensorScalarComparison l E L ι W).hom.app
          ((rationalDerivedTensor l E W).obj (X, Y), Z) ≫
        (rationalDerivedTensor l L W).map
          (Prod.mkHom ((rationalTensorScalarComparison l E L ι W).hom.app
            (X, Y)) (𝟙 _)) ≫
        (pullbackTensorRationalAssociator l L W
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj X)
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj Y)
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj Z)).hom) := by
  sorry

end WeilConjectures
