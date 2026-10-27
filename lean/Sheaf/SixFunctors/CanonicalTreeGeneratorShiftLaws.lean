/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.SixFunctors.RealizationTreeShiftTransport

/-! # Local shift laws for the complete canonical generator collection

Source: blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
map and coefficient comparison sentences; the local-generator step of
lem-pur-integral-realization-shift-coherence.
(blueprint: lem-pur-canonical-tree-generator-shift-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Select every published synchronized basic constructor, retaining its actual maps.
Source: the canonical generator collection in the coefficient-comparison argument
(blueprint: lem-pur-canonical-tree-generator-shift-laws). -/
def canonicalTreeGenerators (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (R : Realizations l E D o) : TreeGenerators l E D o R where
  selected := fun {_} {_} _ _ _ _ {_} {_ _} {_ _ _ _} _ ↦ True

open Classical in
/-- Every synchronized basic canonical system generator has its intrinsic slotwise
shift square, before applying total limit. No integral shift square, realization
intertwining, expression-context closure, or existence of shifted maps is asserted.
Source: blueprint fix-prop-coherence.proof.md, maps-used and coefficient-comparison
sentences; realization-shift assembly step 2
(blueprint: lem-pur-canonical-tree-generator-shift-laws).

Proof: apply systemAdjunctionOpenMapShift to the primitive isomorphisms and their
inverses, pull and open adjunction units and counits, direct-image and open compositors,
and normalized beta and open projection maps. In each designated occurrence use the
actual variableContext. Its other operands are fixed, so naturality also transports
the reduction-shift map at that occurrence. The pull/tensor and associator cases use
the first or signed second tensor comparison as dictated by that context.
For proper/open interchange, use the clopen factorization of lambda and its open
adjunct: the component projection is degreewise (x,y) to (x,0), and the clopen
identification is degreewise identity. Their shift squares paste with the open and
direct-image compositors. Taking the specified open adjunct gives gamma's square.
For exchange in any commutative square, use its actual right-mate formula: the unit,
the primitive pullback-composition square, then the counit. Their global adjunction
shift equations paste, without a cartesianness assumption. Proper projection is the
unit followed by the pull/tensor comparison and the counit tensor identity; use
bifunctoriality in the designated signed slot. Compactification exchange and projection
paste those equations with beta and the open projection. These are the algebraic
calculations underlying properOpenProjectionShift, applied to the actual maps; its
extra intermediate-domain tests and cartesian-only exchange constructor are not
inferred from endpoint admissibility. The primitive cochain equations and adjunction
identities used in this direct pasting hold before bounded-domain restriction.
Support expansion is the identity for the same open/proper composite. Finally use
naturality in the reduction-shift map and the two explicit endpoint equalities to
obtain treeSubexpressionShift on both sides. The argument retains the designated
Koszul sign and applies to every integer, without changing a comparison. -/
theorem canonicalTreeGeneratorSystemShift (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o) :
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e t : Expression _ I X W)
    (_ei : Function.Injective e.occurrenceLabel) (_ti : Function.Injective t.occurrenceLabel)
    (_ge : e.geometric) (_gt : t.geometric)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ)
    (_he : e.domain l E o K) (_ht : t.domain l E o K)
    (_heNew : e.domain l E o (Function.update K i ((K i)⟦r⟧)))
    (_htNew : t.domain l E o (Function.update K i ((K i)⟦r⟧)))
    (s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K))
    (v : e.ringedObj l E R.ringedModels K ⟶ t.ringedObj l E R.ringedModels K)
    (sNew : e.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧))) ⟶
      t.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧))))
    (vNew : e.ringedObj l E R.ringedModels (Function.update K i ((K i)⟦r⟧)) ⟶
      t.ringedObj l E R.ringedModels (Function.update K i ((K i)⟦r⟧)))
    (_g : SynchronizedBasic l E o R.compositors R.openComparisons R.canonicalBridge
      R.properOpen R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
      ((inputReduction l E X).obj K) K
      ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧)))
      (Function.update K i ((K i)⟦r⟧)) e t s v sNew vNew),
    (c : Expression.SlotContext (systemInterpretation l E o) (X i) W) →
    (hc : e.variableContext (systemInterpretation l E o)
      ((inputReduction l E X).obj K) i = some c) →
    (hOld : c.evaluate.obj ((calculus l E (X i).left).reduction.obj (K i)) =
      e.systemObj l E o ((inputReduction l E X).obj K)) →
    (hNew : c.evaluate.obj ((calculus l E (X i).left).reduction.obj ((K i)⟦r⟧)) =
      e.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧)))) →
    (d : Expression.SlotContext (systemInterpretation l E o) (X i) W) →
    (hd : t.variableContext (systemInterpretation l E o)
      ((inputReduction l E X).obj K) i = some d) →
    (kOld : d.evaluate.obj ((calculus l E (X i).left).reduction.obj (K i)) =
      t.systemObj l E o ((inputReduction l E X).obj K)) →
    (kNew : d.evaluate.obj ((calculus l E (X i).left).reduction.obj ((K i)⟦r⟧)) =
      t.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧)))) →
    sNew ≫ (treeSubexpressionShift l E o t K i r d hd kOld kNew).hom =
      (treeSubexpressionShift l E o e K i r c hc hOld hNew).hom ≫ s⟦r⟧' := by sorry

end WeilConjectures.IntegralSystemRealization
