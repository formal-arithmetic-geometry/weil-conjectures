/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.SixFunctors.IntegralExpressionOccurrences
public import Sheaf.SixFunctors.SynchronizedCanonicalMaps

/-! # Reevaluate a canonical construction after shifting one independent input

Source: blueprint fix-prop-coherence.proof.md, coefficient-comparison sentence;
synchronization step in the integral realization-shift argument.
(blueprint: lem-pur-canonical-shift-synchronization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open Classical in
/-- Every old canonical construction has an evaluation at the shifted input family,
with the same constructors and geometric parameters. This asserts existence only:
no system, integral, or realization shift square is included.
Source: blueprint fix-prop-coherence.proof.md, coefficient-comparison sentence;
realization-shift proof, simultaneous construction of the shifted canonical map
(blueprint: lem-pur-canonical-shift-synchronization).

Proof: induct on CanonicalPair, keeping the expression occurrence labels. For a
basic map repeat its BasicPair constructor at the shifted family; for isoHom and
isoInv first repeat the underlying CanonicalIsoPair constructor. Every primitive
constructor preserves the occurrence labels, with tensor operands retaining their
disjoint labels. Thus every intermediate expression is injective in its occurrence
labels when the endpoints are independent. Shifting the selected input preserves
derived completeness and constructibility. Along its unique occurrence path the
cohomological and Tor intervals translate, and the unchanged branches keep their
bounds; enclosing finite unions give common finite intervals. Normalization and
compatible origins are shift stable. Thus all intermediate admissibility witnesses
remain valid. At a basic constructor the supplied realization's completionIso on
the shifted domain gives the completion inverse used by SynchronizedPair.basic;
the original inverse and map are retained. Identity repeats identity. At composition
use the shifted intermediate admissibility just established, and compose the two
inductively constructed maps. At unary contexts apply the same operation to both
new maps. At tensor apply its bifunctor to the two new maps. These are precisely
the synchronized constructors, so the induction yields the required witness,
including all finite outer contexts. For an absent label the subtree is unchanged;
for a present label it is shifted only once. This handles zero and negative shifts,
empty opens, and repeated object values without identifying distinct labels. -/
theorem canonicalShiftSynchronization (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e t : IndependentExpression _ I X W)
    (_ge : e.val.geometric) (_gt : t.val.geometric)
    (K : (e.val.domain l E o).FullSubcategory) (_ht : t.val.domain l E o K.obj)
    (i : I) (r : ℤ)
    (s : e.val.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      t.val.systemObj l E o ((inputReduction l E X).obj K.obj))
    (v : (e.val.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (t.val.evaluate (integralInterpretation l E)).obj K.obj)
    (_hpair : CanonicalPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
      R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
      ((inputReduction l E X).obj K.obj) K.obj e.val t.val s v) :
    ∃ sNew vNew,
      SynchronizedPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
          R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
          ((inputReduction l E X).obj K.obj) K.obj
          ((inputReduction l E X).obj (Function.update K.obj i ((K.obj i)⟦r⟧)))
          (Function.update K.obj i ((K.obj i)⟦r⟧)) e.val t.val s v sNew vNew := by sorry

end WeilConjectures.IntegralSystemRealization
