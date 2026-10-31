/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTowerGeometricAssembly

/-! # Finite normalization of the constructed geometric words

Source: Local pairs and Levels of the geometric coefficient-tower gluing proof.
(blueprint: lem-sp-geometric-finite-word-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Evaluation of the explicit refinement and binary words is the canonical finite word.
This theorem concerns only the two finite normalization equations for already
constructed operations; it constructs neither operations nor a coherent calculus.
Source: Stacks 0F7I--0F7K and Levels in the geometric gluing proof
(blueprint: lem-sp-geometric-finite-word-normalization).

Proof: first conjugate the varying-ring gamma through the fixed semilinear
normalization. The semilinear gamma_evaluation formula gives its actual component,
and gamma_finite identifies that component with the normalized finite proper/open
map on each supplied bounded-below etale origin. The section-pinned graph
coordinates identify the given ordinary push evaluation with this normalization;
taking mates gives the pull and open evaluation squares. Localizing these squares
and cancelling the realization unit/counit pairs yields the exact comparison word
specified by finiteData.evaluation.normalization and fixedSupportCoordinates.
For a refinement expand rho: evaluation takes its inserted proper identity,
gamma and proper compositor to the same finite word. Common-refinement
independence identifies this with fixedRefinement on the supplied origin.
For composition expand the chosen compatible tower word; evaluate its open and
proper compositors and gamma, then use the coefficient/site compatibility for
refinement and composition, with identity coefficient map. Conjugation by the
three common-refinement comparisons gives finiteCanonicalComposition for the
three prescribed compactifications. All these are evaluations of constructed
maps; no equality is inferred from conservativity of evaluation. The empty
scheme, identity arrow and identity refinement cases reduce to the corresponding
unit equations, with the same normalized coordinates. -/
theorem finite_words
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (g : GraphCoordinates l E b o)
    (finiteData : FiniteNormalization l E k b o q z) :
    FiniteWordCompatibility l E k b o q z finiteData (operations l E k b o q z g) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
