/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.SixFunctors.RealizationTreeShiftData

/-! # Context closure of selected generator system squares

Source: the conditional expression-tree argument of
lem-pur-realization-tree-shift-transport, following the coefficient-comparison
sentence of the current blueprint fix-prop-coherence.proof.md.
(blueprint: lem-pur-realization-tree-system-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open Classical in
/-- Selected local generator system squares persist under finite expression contexts.
Only the system square is asserted; no realization square or integral conclusion
is assumed or concluded here.
Source: lem-pur-realization-tree-shift-transport, proof step 7 and the system part
of steps 5--6; current blueprint fix-prop-coherence.proof.md, inherited equations
(blueprint: lem-pur-realization-tree-system-square).

Proof: Induct on the TreeSynchronizedPair derivation, retaining the selected
collection at its basic constructor. Work with subexpressions whose occurrence
labels are injective, rather than requiring each subtree to use every global
label. Check from each actual basic constructor that its two trees have the
same occurrence-label multiset; induction preserves this through the relation.
Thus selected contexts either exist at both ends or are absent at both ends.
If the selected label is absent, pointwise update changes no evaluation;
all generator components are those at the same evaluated operands. If it is
present, variableContext identifies its unique path and the assumed generator
law supplies the basic system square. Identity is immediate. Paste the two
squares for composition, retaining the supplied intermediate admissibility and
geometric witnesses. For a unary context map the child square and apply
naturality of its designated shift. Treat compact support as the same open and
proper composite, including the open intermediate. At a tensor context the
selected label is in exactly one operand. Apply the induction hypothesis there
and naturality of the designated tensor comparison in both operands. This also
handles changes in the spectator operand; use the signed right-slot comparison
when appropriate. At the root the endpoint transports in treeSubexpressionShift
are exactly those of treeSystemShift. Every equality is in the derived system
category before total limit, so no evaluation faithfulness is used. -/
theorem realizationTreeSystemSquare (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    (G : TreeGenerators l E D o R)
    (_hGenerators : TreeGeneratorShiftLaws l E D o R G)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e t : IndependentExpression _ I X W)
      (ge : e.val.geometric) (gt : t.val.geometric)
      (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ)
      (he : e.val.domain l E o K) (ht : t.val.domain l E o K)
      (s : e.val.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.val.systemObj l E o ((inputReduction l E X).obj K))
      (v : (e.val.evaluate (integralInterpretation l E)).obj K ⟶
        (t.val.evaluate (integralInterpretation l E)).obj K)
      (sNew : e.val.systemObj l E o ((inputReduction l E X).obj
          (Function.update K i ((K i)⟦r⟧))) ⟶
        t.val.systemObj l E o ((inputReduction l E X).obj
          (Function.update K i ((K i)⟦r⟧))))
      (vNew : (e.val.evaluate (integralInterpretation l E)).obj
          (Function.update K i ((K i)⟦r⟧)) ⟶
        (t.val.evaluate (integralInterpretation l E)).obj
          (Function.update K i ((K i)⟦r⟧)))
      (pair : TreeSynchronizedPair l E o R.compositors R.openComparisons
        R.canonicalBridge R.properOpen
        R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
        ((inputReduction l E X).obj K) K
        ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧)))
        (Function.update K i ((K i)⟦r⟧))
        (G.selected ((inputReduction l E X).obj K) K
          ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧)))
          (Function.update K i ((K i)⟦r⟧))) e.val t.val s v sNew vNew)
      (heNew : e.val.domain l E o (Function.update K i ((K i)⟦r⟧)))
      (htNew : t.val.domain l E o (Function.update K i ((K i)⟦r⟧))) :
    sNew ≫ (treeSystemShift l E o t K i r).hom =
      (treeSystemShift l E o e K i r).hom ≫ s⟦r⟧' := by sorry

end WeilConjectures.IntegralSystemRealization
