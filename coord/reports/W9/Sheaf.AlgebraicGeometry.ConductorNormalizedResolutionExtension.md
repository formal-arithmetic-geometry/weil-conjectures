## What changed

Constructed the conductor-extended resolution towers explicitly. The unit branch
uses the given tail tower and composes its initial isomorphism with the actual
normalized conductor blowup map. The nonunit branch uses Fin.cases to prepend X,
the conductor ideal, and the actual conductor blowup arrow. All reducedness,
coherence, nonempty support, nowhere density, normalized-blowup witnesses and
regular termination fields are proved. Identity/successor order embeddings prove
the complete existing exact extension predicate, including every arrow and center.

The previously proved preparation section was moved verbatim to the new public
ConductorResolutionPreparation module to avoid a cycle between the item and its
new support lemmas. The item re-exports it with the same public names and meanings.
The main theorem now assembles its tower and comparison fields, constructs the
identity comparison explicitly, derives both identity laws from
the canonical comparison uniqueness, applies the generic composition/surjectivity
laws, proves the empty-input clause and supplies the exact extension
witness. Every existing public signature is unchanged.

Comparisons are selected only from a characterization determining the contraction
indices and actual level maps up to precisely the equalities used downstream;
auxiliary pulled-tower models are immaterial up to their specified isomorphisms.
Tower data is constructed explicitly, never selected from a holed existence claim.

Validation: all five sandbox modules compiled successfully through lcompile.py
(7.2--10.6 seconds per file). The delivery additionally runs the required axiom
probes and server preflight through deliver3.py. The item has
zero current direct Lean importers (confirmed by anchored import search and
tools/downstream.py), so no additional existing consumers require compilation.

## Proved and sorry left

Original holes: 1. Reduced: AlgebraicGeometry.conductor_normalizedResolution_extension
(lem-trf-conductor-extension-of-normalized-resolution). Its assembly proof is now
complete, conditional on the two genuinely smaller comparison statements below.
This is a decomposition, not an axiom-free proof of the original theorem: 0 original
holes proved outright, 1 upper hole eliminated, 2 new lower holes added (net -1).

New fully proved declarations:

- AlgebraicGeometry.rationalConductor_finiteGeneration;
- AlgebraicGeometry.rationalConductor_unit_isIso;
- AlgebraicGeometry.rationalConductorTower_extension;
- AlgebraicGeometry.normalizedResolutionCenter_ne_top;
- AlgebraicGeometry.normalizedResolutionIdentityComparison_levelMap;
- AlgebraicGeometry.normalizedResolutionIdentityComparison (explicit construction).

The concrete definitions conductorPrependedTower and rationalConductorTower contain
no sorry and use only proved property theorems. The former preparation declarations
are unchanged and introduce no holes.

Every remaining sorry in the delivery:

- AlgebraicGeometry.rationalConductorTower_comparison
  (lem-trf-conductor-resolution-comparison): existence and uniqueness on indices
  and actual level maps of a comparison for one smooth map, without rule laws.
- AlgebraicGeometry.normalizedResolutionComparison_laws
  (lem-trf-normalized-resolution-comparison-laws): generic composition
  and surjectivity laws assuming a family of comparisons already given, without
  constructing towers or comparisons or asserting any conductor extension.

Both have complete natural-language arguments and sources in their docstrings and
DAG nodes. Neither is the original theorem with its hypotheses repackaged.

## No longer needed

No mathematical node or module is pruned. The conductor geometry, normalized-blowup
calculus, finite-type Noetherianity and surjective base change remain needed, now
assigned to the relevant preparation, tower or comparison step.

The item no longer directly imports SmoothNormalizedResolutionRule,
ConductorSmoothBaseChange, NormalizedBlowup, CoherentFiniteType,
NormalizedBlowupCalculus or Mathlib.AlgebraicGeometry.Noetherian; all six imports
are preserved in the preparation module and the required public scope is re-exported.
This is an import relocation, not a claim that those dependencies are unnecessary.
No existing source-library declaration or import is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable existing dependency was found. The old plan's
"prepend" step lacked a finite-index tower construction in the library; that
construction and its complete extension specification are now proved. The remaining
comparison steps need an API for attaching/deleting the initial stage and for
uniqueness/coherence of cartesian normalized tower comparisons. These are the two
new lower statements, not an application of the stronger regular-functorial QE rule.

Edge cases checked: unit conductor (all tail indices unchanged), nonunit conductor
(exactly one new stage), zero-length tail, empty input (unit conductor by vacuous
normality and empty preparation because it maps to the empty input), disconnected
inputs, and proper invertible ideals (retained despite isomorphism arrows).
The generic comparison lemma is restricted to reduced finite-type rational base
inputs so its proof can use the published normalized-blowup calculus at every level.

## New nodes

- def-trf-conductor-resolution-preparation: the unchanged conductor preparation
  data and exact extension specification, extracted to break the import cycle.
- lem-trf-conductor-resolution-tower: explicit construction and complete exact
  extension specification, proved using identity or successor embeddings.
- lem-trf-conductor-resolution-comparison: one smooth-map comparison, canonically
  characterized on its ordered retained indices and actual maps; sorry remains.
- lem-trf-normalized-resolution-comparison-laws: composition/surjectivity laws for already supplied cartesian
  comparisons on finite-type rational resolution towers; sorry remains. Identity
  comparison is explicitly constructed and its laws are derived in the item.

All inherit sec-trace-formula/sk-i-curve-zero and the original ancestor attribution.
No unit statement or realized step is bypassed. Mathlib searches used LeanFinder,
Loogle, LeanSearch and grep; hits concern relative normalization and ring conductors,
not this tower calculus. The blueprint search found no conductor node and no matching
normalized-resolution comparison node. Source read: ILO VIII 2.2.1--2.3.5 and
2.3.12, printed pp.90--93.

Change record: coord/changes/conductor-resolution-preparation-module.md.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
