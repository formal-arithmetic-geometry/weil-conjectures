## What changed

Proved both clauses of `AlgebraicGeometry.ProEtale.openComparison_unit_normalization` in
`Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`, with its signature and both
public comparison definitions unchanged. Added three proved private helpers: the general
Hom formula for conjugation, the conjugate of the specified restriction comparison, and
the explicit sectionwise direct-image mate calculation. The two iterated-mate identities
identify the comparisons and Mathlib's unit equation finishes the proof.

Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique`. Updated the existing node's
proof, proof dependencies and proof origin to follow this calculation. Removed obsolete
tool approvals for dependencies no longer used. The unit route is unchanged.

The proof-context commands are documented in
`coord/changes/openComparison-unit-normalization-proof-context.md`; they affect only
elaboration of private helpers. No public signature or definition changes.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.ProEtale.openComparison_unit_normalization`
(node `lem-sf-open-comparison-unit-normalization`). Holes closed: 1; holes added: 0;
remaining holes in the delivered module: 0. This is a proof, with no split-offs.

The completed theorem's `#print axioms` reports exactly `propext`, `Classical.choice`,
and `Quot.sound`. Its proof does not depend on a theorem containing `sorry`.
The unchanged hypotheses cover identity and empty immersions, zero sheaves and the zero ring.

## No longer needed

Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`;
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`;
- `Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation`;
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`;
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`;
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The last five imports were added to the shared source after the retained proof was written.
The inverse-image, comparison-site and etale definitions used by this proof are already
available through the unchanged public imports; their direct imports are redundant.
The pro-etale weakly-etale localization module is not needed by the proof.

Removed proof dependencies:

- `lem-weil-proetale-weakly-etale-localization`;
- `lem-weil-extension-by-zero-adjunction` (the intrinsic presentation theorem);
- `def-weil-proetale-inverse-image`;
- `lem-pur-proetale-open-unit-evaluation`.

The actual theorem uses the already proved fixed-scalar localization adjunctions and
canonical uniqueness isomorphisms. No intrinsic realization transport or tensor-valued
open-unit evaluation theorem is needed. The existing public imports are retained to
preserve the module's published import interface; those imports are not logical proof
dependencies of the completed theorem. No whole-library module withdrawal is asserted.

## Where the brief, the DAG or earlier work was wrong

The original plan passed through intrinsic coefficient realization and the open-unit
evaluation theorem. The stated comparison is instead already expressed in fixed-scalar
sheaves, and both localization isomorphisms are canonical left-adjoint uniqueness maps.
Their identity conjugates permit a direct proof using the existing constructions.
The source is Stacks Project Tag 09AF, `lemma-jshriek-comparison`, lines 5076–5087 of
`literature/stacks-project/proetale.tex`; the refinement for the specified inverse-image
comparison is supplied by the explicit mate calculation. No statement or definition repair
and no consumer adaptation is needed.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
