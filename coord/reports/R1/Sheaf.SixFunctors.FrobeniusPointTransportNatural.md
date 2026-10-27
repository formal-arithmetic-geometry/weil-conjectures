## What changed

Prove `WeilConjectures.frobeniusPointTransport_natural` from chain-level presheaf
naturality, exact derived localization, the specified comparison naturality, rational
scalar localization, and a separate common-stage natural-transformation result. All
existing public signatures and transport definitions are preserved.

The new module `Sheaf.SixFunctors.FrobeniusPointTransportRationalScalar` isolates the
finite coefficient-extension square, which is one clause of the original statement
and the hypothesis needed by common-stage descent. Its docstring and node spell out
the completed-coefficient normalization proof. This is a separate coefficient result,
not a renamed copy of the naturality theorem.

The second new module, `Sheaf.SixFunctors.FrobeniusPointTransportQbarNaturalTransformation`,
isolates common-stage descent and identifies every component with the literal qbar
transport. Its conclusion concerns the algebraically closed transformation alone; it
does not restate the finite, integral, rational or scalar clauses of the item.

The landed declarations used include `inverseImagePullbackComparisonFinite_natural`,
`inverseImagePullbackComparisonIntegral_natural`,
the exact-localization API, together with the
existing uniqueness specifications of the transport, fibre and pullback constructions.
No landed theorem is copied as a new public declaration. No correction to a statement
or definition is proposed.

## Proved and sorry left

Closed in the item: `WeilConjectures.frobeniusPointTransport_natural`.
No sorry remains in the item module. Its finite and integral sigma linearity,
chain naturality, ambient derived naturality, finite and integral transport naturality,
constructible naturality and rational naturality are combined by real
Lean proofs. The qbar clause conjugates the separate natural transformation by
the canonical object equalities; the scalar clause applies the separate coefficient result.

Added hole: `WeilConjectures.frobeniusPointTransportRational_scalar`, node
`lem-weil-frobenius-point-transport-rational-scalar`.

Added hole: `WeilConjectures.frobeniusPointTransportQbar_naturalTransformation`, node
`lem-weil-frobenius-point-transport-qbar-natural-transformation`. Exactly one current
baseline hole is closed and two are added: this is a decomposition, net minus one
closure, rather than a net proof.
The three object-equality lemmas had already been closed by C2 in the current shared
baseline; their proofs here do not claim three additional closures.

## No longer needed

The main proof retains only the proof imports `Sheaf.Paper.IsomorphismComparisonNatural`
and the two new result modules. The following original proof-only imports are removed:

- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.FiniteCoefficientPoint`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`
- `Sheaf.Paper.IsomorphismComparisonScalarExtension`
- `Sheaf.Paper.IsomorphismDerivedPullback`
- `Sheaf.Paper.PointProEtaleSectionsExact`
- `Sheaf.Paper.PointSectionsScalarExtension`
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`

Their statement APIs needed here are already public dependencies of the original
public imports. No public import is removed. The experimental additional
`Sheaf.Paper.PointCompositeComparisonTower` import is also unnecessary in the main file.

The main proof does not import `Sheaf.Paper.PointAutomorphismRestrictionNatural`:
presheaf naturality proves its restriction square directly. It does not import
`Sheaf.Paper.PointTransformationCoefficientDescent`: the rational pure-tensor proof
handles arbitrary rational morphisms directly. The node dependencies
`lem-weil-point-automorphism-restriction-natural`,
`lem-weil-point-automorphism-transport-scalar-extension`, and
`lem-weil-point-transformation-coefficient-descent` are removed from the main node's
proof route. The first two remain in the new coefficient lemma's proof plan.
`lem-weil-point-rational-family-common-stage-naturality` and
`lem-weil-point-composite-comparison-tower` are needed by the new qbar result rather
than directly by the main theorem. No node is claimed globally obsolete. No module
is withdrawn. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned general automorphism transport and coefficient descent use completed
sections with coefficient unlift and explicit normalization isomorphisms. The item
uses literal size-descended small fibre components. Applying the general scalar
equation therefore requires a nontrivial normalization bridge; it is not a direct
`exact` of that equation. The new coefficient lemma records precisely that bridge and
square. The original theorem itself is unchanged and is not disputed.

All experimental edits to coefficient cones and sigma definitions were excluded
from this packet. The proof uses the current library definitions.

## New nodes

`lem-weil-frobenius-point-transport-rational-scalar`, in
`dag/nodes/sec-six-functors/`, records the specified rational coefficient square.
It is strictly part of the original argument: it says nothing about chain,
derived, constructible or arbitrary rational/qbar morphism naturality. Its proof
uses the general automorphism scalar theorem after the recorded normalization
formulas. Identity extensions and zero objects require no extra hypothesis.
No change record is needed because no existing statement or definition changes.

`lem-weil-frobenius-point-transport-qbar-natural-transformation`, in
`dag/nodes/sec-six-functors/`, records common-stage descent of the rational family
and the component formula, before conjugating the naturality square. Its proof plan
uses the existing common-stage family theorem and composite-comparison tower.

Validation: all three modules compiled through `lcompile.py`; the final main-file
profile completed in 58.4 seconds, below the 60-second limit, with only the expected
development-profiler warnings. Those profiler options are removed from the delivery.
The section bridges preserve the function-level HEq specification, avoiding repeated
unfolding of the completed coefficient action. Existing public signatures and both
derived-sigma definition bodies were compared with the current source and are unchanged.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
