/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import WeilConjectures.SixFunctors.OpenInterchangeReduction.StructuralReductionTensorAssociator
import WeilConjectures.SixFunctors.OpenInterchangeReduction.StructuralReductionTensorLeftUnit
import WeilConjectures.SixFunctors.OpenInterchangeReduction.StructuralReductionTensorRightUnit
import WeilConjectures.SixFunctors.OpenInterchangeReduction.StructuralReductionPullComposition
import WeilConjectures.SixFunctors.OpenInterchangeReduction.StructuralReductionPushComposition
import WeilConjectures.SixFunctors.OpenInterchangeReduction.StructuralReductionPullPushUnit
import WeilConjectures.SixFunctors.OpenInterchangeReduction.StructuralReductionPullPushCounit
import WeilConjectures.SixFunctors.OpenInterchangeReduction.StructuralReductionOpenUnit
import WeilConjectures.SixFunctors.OpenInterchangeReduction.StructuralReductionOpenCounit

/-! # Substitution into structural coefficient squares

Source: current blueprint fix-prop-coherence, maps-used sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.OpenInterchangeReduction

/-- Extend the universally quantified short structural squares to admissible
finite substituted words. No open-generator square is a conclusion.
Source: current blueprint fix-prop-coherence.proof.md, maps-used sentence
(blueprint: lem-sf-structural-reduction-word-substitution).

Proof:
Induct through the substituted child words. Normalize each actual whole system and use the actual
reduction/total-limit reconstruction equivalence. Tensor and pullback use the defining quotient-
tower identifications; proper image is the actual total limit. The normalized DVR effectivity and
the compatible etale origins, constructible reductions and common finite intervals reconstruct a
complete constructible finite-Tor integral vertex. The open reconstruction and reduction
comparison supply the same assertion for open extension, including the scalar unit. Each
reconstructed finite reduction is the original system level, so support and Tor bounds stay
unchanged. This is the same finite induction as the short-intermediate domain argument, without
using its length restriction.

Identify the canonical coefficient map of each child with its recursive r. For tensor and pullback
transpose the quotient augmentation identity using the actual adjunction; for proper image use its
actual counit; for open extension transpose u followed by L(r_j), and use the inverse open
reconstruction laws. The counit of a normalized system is invertible. The completion units on
complete finite-Tor constructible objects are invertible. Induction and preservation of
isomorphisms by each functor and both tensor slots therefore give invertibility of both the
recursive completion transport and r at every substituted child. The equations are natural on
whole systems, before finite evaluation.

Replace the one or three child words of a structural generator by independent variables at their
schemes, retaining the scalar unit in a unitor. Use a finite family lifted to the input universe
i. The resulting skeletons have at most two operations. Give these variables the reconstructed
actual integral child values. Transport the original intermediate systems by the preceding r
isomorphisms. Normalization, origins, support and Tor amplitude are invariant under isomorphism,
so these inputs and skeleton endpoints satisfy exactly the assumed short-square domain. Apply the
hypothesized short-square family.

Paste the short square with the naturality squares of the system and ringed structural generators
and the recursive completion transports. At a unary constructor its coefficient comparison is r_A
followed by A(r_child); at tensor it is r_tensor followed by tensor(r_left,r_right). Thus the
pasted vertical arrows are exactly r_B and r_C. The ringed naturality and completion transport
cancel the child completion isomorphisms in the definition of integralMap. Functoriality and
associativity give Assertion for the substituted words. Naturality of tensor constraints follows
from their actual ringed constructions; naturality of compositors and adjunction units/counits
follows from the specified Hom bijections. Repeated variables use diagonal substitution. Identity
maps, empty opens, zero inputs and empty initial input families are covered by the same equations.
-/
theorem structuralReductionWordSubstitution
    {D : FiniteFieldDatum.{u}} (coeff : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic coeff.l) E]
    [FiniteDimensional (Padic coeff.l) E] (o : GeneratorReduction.Operations coeff.l E)
    (hShort : ∀ {S : Type s} (W : S → Scheme.{u})
      (_hW : GeneratorReduction.FiniteTypeFamily W D.k)
      {I : Type i} (location : I → S)
      {a : S} {B C : GeneratorReduction.Word W location a}
      (g : GeneratorReduction.GeneratorKind W location B C),
      Structural g → B.length ≤ 3 → C.length ≤ 3 →
      ∀ (K : ∀ k : I, DerivedCategory (scalarReductionSource coeff.l E (W (location k))))
        (lo hi torLo torHi : ℤ),
        (∀ k : I, GeneratorReduction.Admissible coeff.l E
          (IntegralSystemRealization.calculus coeff.l E (W (location k))) (K k)
          lo hi torLo torHi) →
        B.admissible coeff.l E W location o K lo hi torLo torHi →
        C.admissible coeff.l E W location o K lo hi torLo torHi →
        GeneratorReduction.Assertion coeff.l E W location o K g) :
    StructuralSquares.{u, s, i} coeff.l E D o := by
  intro S W hW I location a B C g hg K lo hi torLo torHi hAdm hB hC
  cases g with
  | tensorAssociator B C T =>
      exact structuralReductionTensorAssociator coeff E o hShort W hW location K lo hi torLo torHi
        hAdm hB hC
  | tensorLeftUnit B =>
      exact structuralReductionTensorLeftUnit coeff E o hShort W hW location K lo hi torLo torHi
        hAdm hB hC
  | tensorRightUnit B =>
      exact structuralReductionTensorRightUnit coeff E o hShort W hW location K lo hi torLo torHi
        hAdm hB hC
  | @pullComposition a b c f g hsf htf hqf hsg htg hqg hs ht hq B =>
      exact structuralReductionPullComposition coeff E o hShort W hW location
        (a := a) (b := b) (c := c) f g hsf htf hqf hsg htg hqg hs ht hq K
        lo hi torLo torHi
        hAdm hB hC
  | @pushComposition a b c f g hsf htf hqf hpf hsg htg hqg hpg hs ht hq hp B =>
      exact structuralReductionPushComposition coeff E o hShort W hW location
        (a := a) (b := b) f g hsf htf hqf hpf hsg htg hqg hpg hs ht hq hp K
        lo hi torLo torHi
        hAdm hB hC
  | @pullPushUnit a b f hs ht hq hp B =>
      exact structuralReductionPullPushUnit coeff E o hShort W hW location
        f hs ht hq hp K lo hi torLo torHi hAdm hB hC
  | @pullPushCounit a b f hs ht hq hp C =>
      exact structuralReductionPullPushCounit coeff E o hShort W hW location
        f hs ht hq hp K lo hi torLo torHi hAdm hB hC
  | @openUnit a b j hj hq B =>
      exact structuralReductionOpenUnit coeff E o hShort W hW location
        j hj hq K lo hi torLo torHi hAdm
        hB hC
  | @openCounit a b j hj hq C =>
      exact structuralReductionOpenCounit coeff E o hShort W hW location
        j hj hq K lo hi torLo torHi hAdm
        hB hC
  | openBaseChange gU j' j g h sq hgU htgU hqgU hg htg hqg hj' hqj' hj hqj B =>
      have hfalse : False := by
        change False at hg
        exact hg
      exact hfalse.elim
  | openTensor j hj hq B C =>
      have hfalse : False := by
        change False at hg
        exact hg
      exact hfalse.elim
  | properOpenInterchange k r p i h hk hki hi hii hr hp B =>
      have hfalse : False := by
        change False at hg
        exact hg
      exact hfalse.elim
  | properOpenLambda k r p i h hk hki hi hii hr hp B =>
      have hfalse : False := by
        change False at hg
        exact hg
      exact hfalse.elim

end WeilConjectures.OpenInterchangeReduction
