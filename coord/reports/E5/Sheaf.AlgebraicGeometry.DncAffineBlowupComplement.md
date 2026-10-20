## What changed

Proved `AlgebraicGeometry.DncAffineBlowup.affine_blowup_complement` in
`Sheaf.AlgebraicGeometry.DncAffineBlowupComplement`, with its original signature,
public imports and six existing definitions unchanged. Added only proved private
helpers for the affine/global comparison, the polynomial chart equivalence,
chartwise strict-transform kernels, the standard-open overlap, and the finite
cover argument. No other Lean module changed.

The proof uses the existing strict-transform/blow-up kernel theorem through
`StrictTransformChart.ker_strictTransformι_eq_ker_pullbackLift`, instead of
rebuilding schematic-image restriction. The actual constant-chart equivalence
has the prescribed constants and parameter formulas. The kernel calculation,
the complement isomorphism, its map to the base, and the parameter-chart ring
identity are all proved. The DAG proof, dependencies and proof origin now
record this route.

Validation: the complete file compiles without warnings. A separate compilation
with `#print axioms AlgebraicGeometry.DncAffineBlowup.affine_blowup_complement`
reported exactly `[propext, Classical.choice, Quot.sound]`. The zero-ring,
zero-generator, nilpotent-generator, zero-divisor and empty finite-list cases
require no nontriviality or regularity assumption in these proofs.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.DncAffineBlowup.affine_blowup_complement`
(node `lem-pur-dnc-affine-blowup-complement`).

Holes added: 0. Holes left in the delivered module: 0. Split-off statements: 0.
Every private helper is proved; this is a complete proof, not a decomposition.

## No longer needed

Removed redundant private imports:

- `WeilConjectures.Blowup.Principalization`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`;
- `WeilConjectures.Blowup.Affine.Defs`;
- `WeilConjectures.Blowup.Gluing`.

The retained public imports already expose the declarations required from these
modules. The finite-generator cover still requires the private import
`WeilConjectures.Blowup.FiniteDegree.Algebra`.

The proof no longer directly requires the planned dependencies
`def-nagata-global-blowup-glue-data`,
`def-nagata-global-blowup-local-model`,
`def-nagata-scheme-theoretic-closure`,
`def-nagata-scheme-theoretic-image`, or
`lemma-nagata-scheme-image-restrict-open`. The existing global chart pullback
and strict-transform kernel results replace those constructions. Removed the
obsolete `lemma-nagata-scheme-image-restrict-open` tool-use entry. All other
approved tool-use entries remain in their original order.

No module is withdrawn and no source-library declaration is removed or changed.
The imports and dependencies used internally by those existing source-library
results remain; the removals above concern this item's direct proof route and
do not claim that these source modules leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was false, and no interface or consumer repair was
needed. The original plan is valid but its separate schematic-closure argument
is unnecessary: the existing Tag 080E kernel theorem supplies it. The finite
hypothesis is used only in the final chart cover. The unit's statement and route
are preserved, with no new node or public declaration.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
