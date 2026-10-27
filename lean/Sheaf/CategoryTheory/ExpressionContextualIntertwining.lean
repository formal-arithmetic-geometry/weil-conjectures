/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Sheaf.CategoryTheory.FiniteFunctorExpressions

/-! # Coefficient equations in arbitrary finite expression contexts

Source: blueprint main-20261015, fix-prop-coherence.proof.md, coefficient-comparison and
inherited-equations sentences; explicit cancellation and context induction in the DAG
(blueprint: lem-sf-expression-contextual-intertwining).
-/

@[expose] public section
set_option autoImplicit false
universe s j w u₁ u₂ v₁ v₂

open CategoryTheory
namespace CategoryTheory.FiniteFunctorExpressions

variable {S : Type s} {C : S → Type u₁} {D : S → Type u₂}
  [∀ a, Category.{v₁} (C a)] [∀ a, Category.{v₂} (D a)]
  {E : ∀ a, C a ≌ D a} (O : Operations.{s, w, u₁, u₂, v₁, v₂} C D E)
  {J : Type j} (loc : J → S)

private theorem unaryComparison_naturality {a b : S} (f : O.Unary a b)
    {M N : D a} (h : M ⟶ N) :
    (E b).inverse.map ((O.A f).map h) ≫ (O.unaryComparison f N).hom =
      (O.unaryComparison f M).hom ≫ (O.barA f).map ((E a).inverse.map h) := by
  dsimp [Operations.unaryComparison]
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    ← (E a).counitInv_naturality h, Functor.map_comp, Functor.map_comp,
    Category.assoc]
  have d := (O.dA f).hom.naturality ((E a).inverse.map h)
  dsimp at d
  rw [d, Category.assoc]

private theorem binaryComparison_naturality {a b c : S} (f : O.Binary a b c)
    {M M' : D a} {N N' : D b} (h : M ⟶ M') (j : N ⟶ N') :
    (E c).inverse.map ((O.B f).map (h, j)) ≫
        (O.binaryComparison f M' N').hom =
      (O.binaryComparison f M N).hom ≫
        (O.barB f).map ((E a).inverse.map h, (E b).inverse.map j) := by
  dsimp [Operations.binaryComparison, Iso.prod, Iso.app]
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  have e : Prod.mkHom h j ≫
      Prod.mkHom ((E a).counitIso.inv.app M') ((E b).counitIso.inv.app N') =
      Prod.mkHom ((E a).counitIso.inv.app M) ((E b).counitIso.inv.app N) ≫
        Prod.mkHom ((E a).functor.map ((E a).inverse.map h))
          ((E b).functor.map ((E b).inverse.map j)) := by
    ext
    · exact ((E a).counitInv_naturality h).symm
    · exact ((E b).counitInv_naturality j).symm
  rw [e, Functor.map_comp, Functor.map_comp, Category.assoc]
  have d := (O.dB f).hom.naturality
    (Prod.mkHom ((E a).inverse.map h) ((E b).inverse.map j))
  dsimp at d
  rw [d, Category.assoc]

/-- Generator coefficient equations persist through every finite parenthesized unary/binary
context, identities, composites and inverses, using exactly the recursive comparisons.
`Paired.generator` assumes only the whole-category coefficient equation, with independently
specified barred transformations. Its binary constructor includes changing either or both
slots, and repeated occurrences. Categories may themselves be the stipulated closed full
subcategories; no evaluation-faithfulness or lifting hypothesis is imposed.

Source: fix-prop-coherence, coefficient comparisons and inherited equations
(blueprint: lem-sf-expression-contextual-intertwining).

Proof: (1) Use the category, functor, naturality and inverse laws of def-nagata-category.
(2) For a generator substitute r_V = R(c_V⁻¹) ≫ e_(M_V). Naturality of e cancels its
invertible target component, giving R(L(h) c_V⁻¹) = R(c_T⁻¹ k).
(3) Naturality of the invertible unit detects equality under R: f = u_Y⁻¹ LR(f) u_X.
Cancel the two comparisons to obtain L(h) ≫ c_T = c_V ≫ k.
(4) Counit naturality followed by LA, and then d_A naturality, proves a_A naturality.
(5) Apply the same calculation on the product category for a_B and an arbitrary pair of arrows.
(6) Induct on the paired derivation. Identity is the functor identity law; at a unary
constructor combine step 4 with the recursive c and the induction hypothesis.
(7) At a binary constructor use step 5 and both induction hypotheses, without a disjointness
condition on inputs or holes. Unchanged children use identity, repeated children use the same
arrow twice. (8) Composition follows from functoriality and the two intertwining equations.
(9) For inverses multiply the established equation by the inverse arrows and comparisons.
(10) These calculations always use the recursive comparisons at the same syntax trees.
(11) They apply in the restricted categories verbatim; empty categories or symbol sets
leave vacuous or identity cases. None requires invertibility of a generator. -/
theorem expression_contextual_intertwining {a : S} {V T : Expression O loc a}
    {h : V.evalD ⟶ T.evalD} {k : V.evalC ⟶ T.evalC}
    (p : Paired O loc V T h k) (K : ∀ i, C (loc i)) :
    (E a).inverse.map (h.app ((reducedInputs (E := E) loc).obj K)) ≫
        (Expression.comparison O loc T K).hom =
      (Expression.comparison O loc V K).hom ≫ k.app K := by
  induction p with
  | @generator a V T h k coefficient =>
    have eqn := coefficient K
    dsimp [Expression.coefficientComparison] at eqn
    rw [Category.assoc, ← (E a).counit_naturality,
      ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
      ← Functor.map_comp] at eqn
    have eqn' := (E a).functor.map_injective
      ((cancel_mono ((E a).counitIso.hom.app _)).mp eqn)
    apply (cancel_epi (Expression.comparison O loc V K).inv).mp
    simpa [Category.assoc] using congrArg
      (fun t ↦ t ≫ (Expression.comparison O loc T K).hom) eqn'
  | identity V => simp
  | comp p q ihp ihq =>
    simp only [NatTrans.comp_app, Functor.map_comp]
    rw [Category.assoc, ihq, ← Category.assoc, ihp, Category.assoc]
  | inverse h k p ih =>
    apply (cancel_epi ((E _).inverse.map (h.hom.app _))).mp
    apply (cancel_mono (k.hom.app K)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp]
    exact ih.symm
  | unary f p ih =>
    dsimp [Expression.comparison, Expression.evalD, Expression.evalC]
    rw [← Category.assoc, unaryComparison_naturality,
      Category.assoc, ← Functor.map_comp, ih, Functor.map_comp, Category.assoc]
  | binary f p q ihp ihq =>
    dsimp [Expression.comparison, Expression.evalD, Expression.evalC, NatTrans.prod']
    rw [← Category.assoc, binaryComparison_naturality,
      Category.assoc, ← Functor.map_comp]
    rw [Category.assoc, ← Functor.map_comp]
    congr 2
    exact Prod.ext ihp ihq

/-- An invertible unbarred transformation in the generated contextual calculus has an
invertible independently specified barred transformation, so the inverse constructor loses
no cases by requesting both isomorphisms.
Source: fix-prop-coherence, inherited equations, contextual lemma step 9
(blueprint: lem-sf-expression-contextual-intertwining).

Proof: apply expression_contextual_intertwining at each input. It expresses k_K as
c_V⁻¹ ≫ L(h_K) ≫ c_T, a composite of isomorphisms when h is invertible. The component
inverses form the inverse natural transformation, by naturality of k. This is precisely
step 9 of the node, and applies to any paired composite or context. -/
theorem expression_contextual_intertwining_isIso {a : S} {V T : Expression O loc a}
    {h : V.evalD ⟶ T.evalD} {k : V.evalC ⟶ T.evalC}
    (p : Paired O loc V T h k) [IsIso h] : IsIso k := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have eqn := expression_contextual_intertwining O loc p K
  have formula : k.app K = (Expression.comparison O loc V K).inv ≫
      (E a).inverse.map (h.app ((reducedInputs (E := E) loc).obj K)) ≫
        (Expression.comparison O loc T K).hom := by
    simpa [Category.assoc] using congrArg
      (fun f ↦ (Expression.comparison O loc V K).inv ≫ f) eqn.symm
  rw [formula]
  infer_instance

/-- Equal composites of generators and contexts have equal independently specified barred
transformations. Endpoint comparisons are the same prescribed, parenthesized comparisons.
Source: fix-prop-coherence, inherited equations, contextual lemma step 10
(blueprint: lem-sf-expression-contextual-intertwining).

Proof: apply expression_contextual_intertwining to each derivation at every K. Evaluating
h = h' at RK and applying L makes the left sides equal. Cancel the common invertible c_V
to get k_K = k'_K. Natural transformation extensionality gives k = k'. This is step 10
of the node, using steps 1--9 for each derivation; step 11 permits the stated full-subcategory
restrictions. No faithfulness of either evaluation functor is used. -/
theorem expression_contextual_intertwining_eq {a : S} {V T : Expression O loc a}
    {h h' : V.evalD ⟶ T.evalD} {k k' : V.evalC ⟶ T.evalC}
    (p : Paired O loc V T h k) (q : Paired O loc V T h' k') (equal : h = h') :
    k = k' := by
  ext K
  apply (cancel_epi (Expression.comparison O loc V K).hom).mp
  rw [← expression_contextual_intertwining O loc p K,
    ← expression_contextual_intertwining O loc q K, equal]

end CategoryTheory.FiniteFunctorExpressions
