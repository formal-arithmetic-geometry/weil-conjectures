## What changed

Replaced the single unfinished proof of
`AlgebraicGeometry.Scheme.FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin_hom`
by the open/proper scalar-mate pasting argument. The canonical comparison data move
verbatim to `Sheaf.Paper.FiniteCompactSupportScalarTransportData`, publicly
re-exported by the assigned module, so the two independent factor statements can
refer to them without an import cycle. Existing names, signatures, attributes,
definitional bodies and public import closure are preserved.

`Sheaf.Paper.FiniteCompactScalarCoordinates` constructs the open realization,
open site and proper site comparison isomorphisms as explicit composites of the
existing canonical maps. There is no choice from an existence theorem. The item
proves the adjunction-transpose pasting, naturality pasting and the factorization
of the original compact-support site comparison into these coordinates. The two
new factor modules are proof imports of the item. The original two proof imports
are needed by the proper factor and move there.

The complete item compiles without warnings through `lcompile.py` (17.3 seconds).
The new coordinate and factor modules and all four unchanged direct importers
(`ExceptionalFiniteScalarMates`, `FiniteCompactSupportScalarComparison`,
`MixedCupCoefficientData`, `ProperEtaleOriginScalarData`) also compile successfully
through the service, which enforces the 60-second Lean acceptance limit. Temporary
consumer copies were removed after verification.
A textual comparison also verifies the original theorem signature and all nine
original comparison definitions verbatim.

Change record: `coord/changes/R4-finite-compact-scalar-data.md`.

## Proved and sorry left

One original hole is closed:
`AlgebraicGeometry.Scheme.FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin_hom`.
The item has zero remaining holes. Its assembly proof is complete, conditional on
the named factor statements below. This is a decomposition, not a net proof gain:
one hole closed, two holes added, net minus one.

Two public theorem holes are added, each exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.FiniteCompactScalar.openScalar_transport`, node
  `lem-finite-open-scalar-transport`, module `Sheaf.Paper.FiniteOpenScalarTransport`.
  This is only the open immersion square, for ambient complexes; it contains no
  proper image or compactification.
- `AlgebraicGeometry.Scheme.FiniteCompactScalar.properScalar_transport`, node
  `lem-finite-proper-scalar-transport`, module `Sheaf.Paper.FiniteProperScalarTransport`.
  This is only the proper direct-image square on bounded-below inputs; it contains
  no extension by zero or compact-support composite.

Each has its source, complete proof in words, edge-case discussion and a matching
DAG node. All other delivered definitions and private lemmas have complete bodies.

## No longer needed

No mathematical dependency or module is pruned. The original data definitions
still use the original dependencies. The two original proof imports move to the
proper factor, where the normalization argument needs them. No source-library
declaration is removed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node cites Steps 7–10 of the coefficient-reduction argument. In the
current `literature/blueprint/latest` proof, the corresponding reduction is Step 5.
The new nodes and updated proof origin cite that current location.

The existing interfaces provide isomorphisms but do not state the two normalized
intrinsic scalar squares needed to identify this particular map. Generic mates
and left-adjoint uniqueness alone do not supply the missing realization/site
compatibility. These are separated into the two strictly smaller factor steps,
rather than replacing the target by an isomorphic-endpoints assertion. No
statement is disputed or weakened. Zero rings, empty schemes and identity scalar
maps are included in the arguments.

## New nodes

`lem-finite-open-scalar-transport` records the unit-preserving comparison for open
extension by zero. Its proof uses the common right-adjoint restriction square,
the realization equivalence unit and naturality in the chosen scalar origin.

`lem-finite-proper-scalar-transport` records the proper comparison. Its proof uses
the existing fixed-site scalar mate, bounded-below comparison and the normalized
K-injective realization comparison. Both are independent mathematical factors of
the original argument, and neither repackages its full hypotheses and conclusion.

Change record: `coord/changes/R4-finite-compact-scalar-data.md`.

`def-finite-compact-scalar-transport-data` attaches the relocated, unchanged nine
comparison constructions to their new data module. It is a definition record,
not a new theorem or proof hole.

`def-finite-compact-scalar-coordinates` attaches the three explicit open/proper
coordinate constructions to their helper module. It adds no compatibility claim
and no proof hole. These records repair the first delivery preflight's missing
module attachments. The search records now also include an actual LeanSearch
query, in addition to Loogle/LeanFinder and Mathlib-source grep.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
