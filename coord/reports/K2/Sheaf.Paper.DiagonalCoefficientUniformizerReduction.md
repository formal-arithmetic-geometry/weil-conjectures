## What changed

Restored the assigned quarantined module from the path in coord/rework.tsv, retaining its
exact theorem signature and its existing public imports. Replaced the original sorry by
an explicit construction of the quotient diagonal arrow and all three traces. Each trace
is the scalar image of the integral trace conjugated by its specified invertible scalar
mate and endpoint. Cancellation proves the diagonal and three trace squares. The existing
CategoryTheory.integration_transport proves both integration identities using the two
normalized supported-source squares. The resulting Diagram and ScalarCompatibility are
constructed by the proved private helper scalarFrame_diagram in the item module,
rather than assumed in a new theorem.

Two new modules isolate the remaining comparison constructions. DiagonalUniformizerScalarFrame
parameterizes its comparison structure by arbitrary coefficient rings and lines: it contains
endpoints, restriction squares and normalized supported sources, with no class, trace or
integration assertion. Its existence theorem specializes this structure to the actual
uniformizer quotient. DiagonalUniformizerFiniteNormalization identifies an already supplied
scalar-compatible quotient diagram with the fixed finite Cartier class and trace at r=n.
The item explicitly inserts these witnesses into the original QuotientCompatibility.

The concrete first version of the frame exceeded the file time limit. Its generic coefficient
parameters avoid repeatedly elaborating the large quotient-ring and tensor definitions.
Local irreducibility of the quotient endpoint definitions also keeps the finite-normalization
statement small. No shared definition or existing module other than the item was changed.
Development profiler options and diagnostic modules were removed before delivery.

## Proved and sorry left

This is a decomposition, not an unconditional proof of the original comparison. The original
hole in AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCoefficient_uniformizerFiniteComparison
is replaced by a complete Lean proof from two strictly smaller comparison obligations.
The item has zero direct sorries. One original hole is closed and two holes are added:

- AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_scalarFrame,
  node lem-diagonal-uniformizer-scalar-frame, in DiagonalUniformizerScalarFrame.
- AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_finiteNormalization,
  node lem-diagonal-uniformizer-finite-normalization, in DiagonalUniformizerFiniteNormalization.

The explicit arrow construction, three trace squares, scalar compatibility, and two transported
integration identities contain no holes. Neither remaining theorem is the original assertion
renamed: the first contains no diagonal arrow or trace at all, while the second takes an
already constructed quotient diagram and scalar compatibility and only establishes its finite
normalization. No definition uses an unproved existence theorem to choose data.

## No longer needed

No public import was removed and no module or DAG node is withdrawn. The original limit,
trace, Cartier, and projective-line cohomology dependencies remain needed for finite
normalization. They now occur below its dedicated node rather than directly in the item's
formal assembly. The item additionally uses the existing integration-transport lemma and
the canonical right-derived model through its new frame module.

The annihilator and finite-root existence declarations are not invoked: the item's unchanged
hypotheses already supply annihilation and normalized finite roots. This is not a claim that
those nodes are unused by other parents. No unit route was bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned source was absent from lean/ because it was quarantined after the
SfP1ChartExchange build failure, not because its mathematical obligation was withdrawn.
Its preserved source was restored, and its Lean attachment and dependencies were kept.
The available declarations describe completed limits, finite Cartier classes and finite
traces, but do not directly supply the normalized quotient scalar frame or identify a
scalar-reduced diagram with the finite presentation. Those missing bridges are now separate,
explicit obligations; the formal construction and integration transport are implemented.

LeanFinder, Loogle and the search-service grep were run before introducing the bridges.
The grep service returned no hits; filesystem rg found the existing endpoint and comparison
definitions and the proved integration_transport lemma. Blueprint searches for
"uniformizer scalar frame" and "uniformizer quotient" returned no matching blueprint nodes.
Edge cases checked: n=0 still uses the positive exponent l; ramified uniformizers are not
replaced by ell-power levels; empty schemes and zero coefficient modules are permitted;
the argument assumes no flatness of the quotient map and makes no inference that equality
of all separate finite reductions detects arbitrary derived arrows.

## New nodes

lem-diagonal-uniformizer-scalar-frame records the independent scalar-frame existence
construction, with its actual endpoint and supported-source fields in Lean and a full
proof in words. The structure is generic in both coefficient rings, so it avoids unfolding
concrete quotient tensors in every field. Its existence theorem is the first new hole.

lem-diagonal-uniformizer-finite-normalization records finite coefficient realizations,
root-normalized quotient-line identifications and the finite Cartier/trace equations for
an already supplied scalar-compatible quotient diagram. Its finite killing exponent is
fixed to r=n; the main proof performs the original existential packaging. This is the
second new hole. No change record is needed: existing public statements and definitions
retain their signatures and bodies, and all additional definitions live in new modules.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
