/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QbarCompactSupportExchangeModel
import WeilConjectures.AlgebraicGeometry.RationalCompactSupportCoefficientCoherence

/-! # Construction of the normalized compact-support coefficient model

Source: blueprint `thm-cbc-qbar`, coefficient coherence and descent paragraphs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard pbcIntegralDatum
  AdicCoefficientDatum.completedPull cbcDerivedOpenShriek
  cbcScalarSourceInverse cbcScalarTargetInverse CbcScalarInverseBetaSpec

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [QuasiCompact f]
  [IsNoetherian X] [IsNoetherian Y']
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

/-- The coherent compact-support and completed-pullback families assemble into the
normalized composite model, without asserting invertibility of its exchange.

Source: blueprint `thm-cbc-qbar.proof`, coefficient-coherence and descent paragraphs,
expanded in proof steps 2--3 of node `thm-cbc-qbar`.
(blueprint: lem-cbc-qbar-exchange-model-exists).

Proof: apply rationalCompactSupportCoefficientCoherence with the four dimension and
invertibility witnesses installed as Fact instances. Write H, H', P, P' for its
normalized compact-support and completed-pullback families, and eta for its compatible
exchange. Use P.comparison and P'.comparison as the two ambient scalar maps; their
completionUnit fields give the required unit equations. Restrict each ambient composite
to integral objects, using H.preserves followed by P.preserves for the source, and
P'.preserves followed by H'.preserves for the target. Compose H.family with P.family,
and P'.family with H'.family, with the inherited exactness and shift structures.
Their localization equations follow by whiskering the two constituent localization
equalities and identifying the two restrictions of each ambient composite: both have
exactly its object and arrow maps. For the source inverse beta, expand the beta of the
composite family, substitute H.beta and P.beta, and use naturality to move the scalar
integral comparison between the two factors. Adjacent comparison inverses cancel.
Functoriality combines the open inverse mate followed by the proper inverse counit
comparison into cbcScalarSourceInverse. For the target use P'.beta and H'.beta in
the opposite composite order, obtaining cbcScalarTargetInverse. Scalar preservation
and the two restriction witnesses supply both membership proofs. These calculations
include equality of fields, since all constituent beta laws include identity fields.
Use eta as exchange. Its normalized equation is the one supplied by coefficient
coherence; the membership witnesses agree by proof irrelevance. Thus every model
field is supplied, with no invertibility assumption and no choice of an arbitrary
coefficient comparison. -/
theorem cbcQbarExchangeModel_exists
    [IsSeparated f] [LocallyOfFiniteType f]
    [IsNoetherian Y] [IsNoetherian X']
    (dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (invY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (invX' : ∀ x : X', IsUnit (l : X'.presheaf.stalk x)) :
    Nonempty (CbcQbarExchangeModel l Ω c c' gbar properSquare openSquare) := by sorry

end AlgebraicGeometry.Scheme
