## What changed

Reduced the original theorem to five distinct parts of its recorded localization argument:
source localization on good representatives; scalar localization with its unit and associator;
descent of eta and the two scalar comparison maps; and descent of the forward purity square
and source unit/composition equations; and the final exceptional equations. The main theorem
combines those results and proves its inverse purity square by taking inverses of an equality of composed isomorphisms.
The fifth interface isolates the equations supplied by the fixed exceptional system.
The coordinate module respects the existing irreducibility annotations during the adjunction
elaboration to prevent expensive automatic unfolding.

Moved the unchanged coordinate definitions into `Sheaf.Paper.RationalScalarComparisonData`
to let the five new helper modules import them without an import cycle. The original module
publicly re-exports the definitions; Result and the original theorem stay there with their
original signatures, and the body of Result is unchanged.
Change record: `coord/changes/E1-rational-scalar-comparison-data.md`.

The current blueprint source read is the coefficient-change proof, parts (2)-(3), and
`sk-prop-sp-rational-adjunction.proof.md`, parts (1)-(2). The unit's localization and
coefficient-change route is retained. Searches in the library, LeanFinder, LeanSearch, Loogle
and Mathlib found generic localization/counit calculus but no complete specialized theorem.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.RationalScalarComparisonIdentification.rationalScalarComparisonIdentification`
by a complete proof from the five new intermediate theorems. This is a decomposition,
not a complete proof of the mathematics: one upper hole closed, five lower holes added,
net -4 holes. No sorry remains in the assigned module or in a definition.

The five remaining holes are exactly:

- `WeilConjectures.RationalScalarComparisonIdentification.rationalPuritySourceLocalization`
  (`lem-pur-rational-source-localization`).
- `WeilConjectures.RationalScalarComparisonIdentification.rationalPurityScalarLocalization`
  (`lem-pur-rational-scalar-localization`).
- `WeilConjectures.RationalScalarComparisonIdentification.rationalPurityComparisonDescent`
  (`lem-pur-rational-comparison-descent`).
- `WeilConjectures.RationalScalarComparisonIdentification.rationalPurityCoherenceDescent`
  (`lem-pur-rational-purity-coherence-descent`).
- `WeilConjectures.RationalScalarComparisonIdentification.rationalExceptionalFinalEquations`
  (`lem-pur-rational-exceptional-final-equations`).

Each is a public theorem in a separate module, with its source and complete proof in words
in its docstring and its matching node. None is the original Result under another name.
The main proof additionally supplies the inverse-square equation. Edge cases reviewed:
repeated fields, three-field chains, d=0, empty schemes, zero objects, and all integer shifts. No witness of an
underdetermined existence theorem is used to define any data.

## No longer needed

No mathematical dependency is claimed globally pruned by this partial reduction. The old
nine-step plan is divided among the five intermediate nodes; its substantive dependencies
remain needed there. No declaration or module is withdrawn. Original public imports move
with the unchanged coordinate definitions and remain transitively public.

The following unused direct proof imports were removed from the coordinate module; the
remaining mathematical obligations and their DAG references are retained in the five helpers:

- `Sheaf.SixFunctors.IntegralLocalizingCompactSupport`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Paper.ScalarCompletionAssociator`.
- `Sheaf.Paper.CompletedScalarChainShift`.
- `Sheaf.Paper.PbcRationalTransport`.
- `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`.
- `Sheaf.Paper.QcqsCompactSupportRealization`.
- `Sheaf.SixFunctors.RationalOperations`.
- `Sheaf.Paper.IntegralTwistScalarCoherence`.
- `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction`.
- `Mathlib.CategoryTheory.Adjunction.Mates`.


## Where the brief, the DAG or earlier work was wrong

The original dependencies provide generic exact localization, tensor comparisons, and
counit normalization, but do not directly state the specialized good-representative source
identification or its combined rational descent. The remaining glue is now made explicit
in five independently provable interfaces. The source normalization is retained, including
the goodness conjunct, so it cannot be satisfied vacuously by a missing good shifted line.
The source localization step retains I explicitly, so its supplied integral source
exactness and linearity can be used without reconstructing those properties.

## New nodes

`def-pur-rational-scalar-comparison-data` attaches the existing coordinate definitions in
the new shared module; no new mathematical definition is introduced.

`lem-pur-rational-source-localization` isolates construction and normalization of the
localized twisted pullback, with exactness and integer-shift compatibility.

`lem-pur-rational-scalar-localization` isolates the ordinary/strict scalar comparison,
its published rational shift and exactness, and its two scalar coherence equations.

`lem-pur-rational-comparison-descent` descends the integral purity and source comparisons,
identifying the exceptional comparison by the fixed counit transpose.

`lem-pur-rational-purity-coherence-descent` transports the forward purity square and
source unit/composition equations. It assumes neither the inverse square nor those source
coherence conclusions. Its integral presentation uses the residue-Tor theorem.

Change record: `coord/changes/E1-rational-scalar-comparison-data.md`.

`lem-pur-rational-exceptional-final-equations` isolates the fixed system equations in
the rational coordinate wrappers: localization shifts, counit transpose, unit and composition.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
