/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum

/-! # Perfect evaluation through a fully faithful closed embedding -/

@[expose] public section
set_option autoImplicit false
universe a b c d
open CategoryTheory Opposite
namespace WeilConjectures

/-- Reflect perfect evaluation through the normalized closed embedding.
Source: Stacks Project, Tag 08JJ, evaluation and restriction argument; the
closed-model normalization of blueprint def-sf-datum
(blueprint: lem-sf-closed-embedding-perfect-evaluation).

Proof: write F for the composite inclusion. Full faithfulness and the Hom
comparison identify its tensor-right adjunction with the restriction of the
ambient tensor-right adjunction. The tensor comparison and source unitors
identify F(I) tensor F(M) with F(M). For an ambient dualizable F(K), use the
ambient evaluation isomorphism first with F(I), then with F(M). Tensor
associativity identifies Hom(F(K),F(I)) tensor F(M) with Hom(F(K),F(M).
Transpose the comparison: the evaluation equation fixes its adjunct, and the
symmetry equation puts the dual on the left. The triangle identities remove
the source unitors. Thus this is the image of the source canonical comparison,
up to invertible comparisons. It is invertible, and full faithfulness reflects
invertibility. This argument includes zero objects and the empty perfect model. -/
theorem closedEmbedding_perfectEvaluation
    {B : Type a} [Category.{b} B] {A : Type c} [Category.{d} A]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} (M : SixFunctorClosedDomain P Q H)
    {H' : Aᵒᵖ × A ⥤ A} (N : CoefficientClosedStructure H')
    (s : @SymmetricCategory _ _ N.monoidal) (F : B ⥤ A)
    [F.Full] [F.Faithful] (e : SixFunctorAmbientClosedModel M N s F)
    (O : A) (o : N.monoidal.tensorUnit ≅ O) (K L : P.FullSubcategory)
    (h : ∀ T : A, IsIso (ringedSiteDualEvaluationLeft N s O o (F.obj K.obj) T)) :
    IsIso (ringedSiteDualEvaluationLeft M.closed M.symmetric
      M.closed.monoidal.tensorUnit (Iso.refl _) K L) := by sorry

end WeilConjectures
