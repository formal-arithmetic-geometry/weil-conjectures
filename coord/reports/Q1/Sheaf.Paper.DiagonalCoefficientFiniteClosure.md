## What changed

The item now constructs the algebraic-closure diagram explicitly by scalar transport
from the bottom finite field. Its diagonal and all three traces are written as
conjugates by the prescribed endpoints and scalar/direct-image mates. The two
integration equations follow from `CategoryTheory.integration_transport`.

The fixed integral and rational diagrams are retained. Their two given compatibility
records are composed from the common Z_l source. The actual coefficient maps and
root maps satisfy the required triangle equations; their proofs use continuous
sections, finite root projections, the normalized rational tensor formula, and
colimit legs. The rational and closure line maps are proved semilinear.

Added `DiagonalScalarCompatibilityTriangle`, `DiagonalClosureLineComparison`, and
`DiagonalClosureScalarFrame`. The first isolates formal composition/cancellation
of normalized scalar compatibilities; the second isolates the geometric bounded
comparison on one shifted rational root line for a qcqs morphism. The third is
proved: it assembles the three line comparisons, regular scalar endpoints and
existing normalized supported-source comparisons into a closure scalar frame.

All new imports of the item are proof imports. No existing signature, definition,
attribute, public import, source-library file or consumer is changed. The item node
and the three new nodes describe the implementation.

Validation: `lcompile.py --all` compiled all four delivery modules successfully.
Separate diagnostic checks also compiled the concrete map-coherence helpers,
the explicit class/trace transport, and the complete family-coherence argument.
All diagnostic modules and profiling options were removed before the integrated check.

## Proved and sorry left

Closed the item's one textual hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCoefficient_finiteClosure`
(node `lem-sfb-diagonal-finite-coefficient-closure`).

Added two holes, each a whole named public theorem in its own new module:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.scalarCompatibility_triangle`
  (`lem-diagonal-scalar-compatibility-triangle`). This has no closure, finiteness,
  filtered-colimit, or family assertion. It concerns composing/cancelling three
  compatibilities and explicitly assumes semilinearity of the second line map.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalClosure_lineComparison`
  (`lem-diagonal-closure-line-comparison`). This has no class, trace, support,
  integration identity or family. It concerns one line endpoint and one normalized
  direct-image mate, on a single root line shifted by two, for one qcqs morphism.

`diagonalClosure_scalarFrame` is proved from the second new theorem and existing
declarations. The private transport and map-coherence helpers are proved. There
is no sorry in the item, a definition, or a private declaration. This is a
one-to-two decomposition, not a complete proof without sorry-dependent inputs;
the two added holes exceed the one closed hole by one. The existing dependency
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_supported_scalar_source`
still has its prior hole; this delivery does not add or move that hole. The reused
regular scalar-extension and flat endpoint constructions are proved in the current source.

## No longer needed

No existing import is removed and no module or declaration is withdrawn. No global
pruning is claimed. The original direct analytic dependencies (Cartesian
coefficients, coefficient colimits, bounded continuity, and exact filtered
colimits) are now assigned to the single-line comparison node, rather than
repeatedly rebuilding a closure diagram from the whole family. The closed-support
comparison is used through `diagonal_supported_scalar_source`; its underlying
exactness dependency remains needed. Canonical right-derived models and
`integration_transport` remain used in the scalar-frame construction.

The item does not use `diagonalCoefficient_finiteExtension`, construct replacement
finite diagrams, or require ambient unbounded coproduct continuity. No unrelated
uniformizer comparison is invoked: `DiagonalUniformizerScalarFrame` is imported
for its existing `ScalarFrame`, `scalarRightDerived`, regular endpoint and endpoint
uniqueness constructions.

## Where the brief, the DAG or earlier work was wrong

The old plan listed general coefficient and continuity theorems but had no
normalized scalar composition/cancellation theorem. A normalized Endpoint for a
composite underlying line map does not by itself prove that the second map is
semilinear: an additive projection of a proper field extension can fix the base
field without being linear over the extension. The new triangle statement
therefore explicitly requires the second map's semilinearity at both line
endpoints; the item supplies it from the actual rational-transition and closure
action formulas, or directly from the given rational compatibility.

The existing source theorem for E-to-closure direct-image comparison on all
unbounded objects requires an additional coproduct-continuity hypothesis. It is
not used. The new geometric obligation asserts invertibility only on the shifted
root line, to which bounded qcqs continuity applies. The unit route is retained.

## New nodes

`lem-diagonal-scalar-compatibility-triangle` records the generic normalized scalar
triangle equivalence with explicit second-leg semilinearity, in
`Sheaf.Paper.DiagonalScalarCompatibilityTriangle`.

`lem-diagonal-closure-line-comparison` records the line endpoint and normalized
qcqs direct-image comparison on the single shifted rational root line, in
`Sheaf.Paper.DiagonalClosureLineComparison`.

`lem-diagonal-closure-scalar-frame` records the proved assembly of a closure scalar
frame from the preceding single-line comparisons and existing support machinery,
in `Sheaf.Paper.DiagonalClosureScalarFrame`.

No change record is needed: all existing interfaces are preserved and the only
existing module changed is the assigned item.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
