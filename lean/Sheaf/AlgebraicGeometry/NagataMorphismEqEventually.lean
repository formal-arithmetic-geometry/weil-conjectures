/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.NagataMorphismEqualityStage

/-!
# Eventual equality of descended morphisms

Source: literature/blueprint/master/blueprint/sec-nagata-compactification/
sk-prop-nagata-sketch-approximation/lemma-nagata-morphism-eq-eventually.md,
node order 356 (blueprint: lemma-nagata-morphism-eq-eventually).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For every stage above the selected equality stage, the two base-changed
morphisms are equal.
Source: blueprint node order 356; Stacks Project, Tag 01ZM (3), proof
(blueprint: lemma-nagata-morphism-eq-eventually).

Proof:
1. The choices in `def-nagata-morphism-equality-stage` give the compact inverse-image
   opens W1 and W2, their selected equality stages lambdaJK, affine covers U of their
   intersections, and coefficient equality stages mu for all target generators.
   By `lemma-nagata-directed-finite-upper-bound`, the selected finite upper bound
   dominates i₀, every lambdaJK and every mu.
2. At any lambda above that bound, `lemma-nagata-qc-open-eq-eventually`, applied
   with X₀ as its base-changed scheme, makes the two transported opens equal.
   Thus the inverse images of the U cover each transported W1. Since the target
   charts cover Y₀, the W1 cover X₀, and these U together cover X_lambda.
3. Transport each coefficient equality from its mu to lambda by the transition
   map on sections. The two maps from each U to its affine target chart agree
   on all algebra generators and on the base ring, since both lie over the same
   base chart. They are therefore equal as algebra maps, hence as scheme maps.
   The two base-changed maps on U have equal projections to Y₀ and S_lambda;
   the fibre-product universal property makes them equal. Open-cover
   extensionality then gives equality on X_lambda. -/
theorem nagataMorphismEqEventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} {hc : IsLimit c}
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i₀ : I} [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    {p : X₀ ⟶ D.obj (op i₀)} {q : Y₀ ⟶ D.obj (op i₀)}
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    {phi psi : X₀ ⟶ Y₀} {hphi : phi ≫ q = p} {hpsi : psi ≫ q = p}
    {d : I → I → I} {r : LinearOrder I}
    (data : NagataMorphismEqualityStageData D c hc i₀ p q phi psi hphi hpsi d r)
    : ∀ (lambda : I) (hlambda : i₀ ≤ lambda),
      nagataMorphismEqualityStage data ≤ lambda →
      ((Over.pullback (D.map (homOfLE hlambda).op)).map
          (Over.homMk (U := Over.mk p) (V := Over.mk q) phi hphi)).left =
        ((Over.pullback (D.map (homOfLE hlambda).op)).map
          (Over.homMk (U := Over.mk p) (V := Over.mk q) psi hpsi)).left := by
  sorry

end AlgebraicGeometry
