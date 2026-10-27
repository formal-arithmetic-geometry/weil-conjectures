## What changed

Proved all three theorem holes in
`Sheaf.CategoryTheory.NormalizedComparisonAugmentedResolution` without changing any
existing statement, definition, attribute or import. A proved private helper handles
naturality of a single augmented computation and is applied to both E and H.

The localization instance follows from Mathlib's localization of the homotopy category
and reflection of isomorphisms by the fully faithful inclusion of D⁺. The normalized
comparison follows by naturality of b, cancellation of the augmentation isomorphism,
and the supplied normalization equation. The final comparison square is naturality
of the termwise isomorphism followed by localization. This implements the existing
five-step DAG plan, using its two Mathlib dependencies already publicly imported.

## Proved and sorry left

Closed 3 original holes:

- `CategoryTheory.augmentedResolution_isIso_Q_map`.
- `CategoryTheory.normalizedComparison_augmentedResolution`.
- `CategoryTheory.augmentedResolutionComputation_naturality`.

All three realize `lem-pur-normalized-comparison-augmented-resolution`.
Added holes: 0. Remaining holes: 0. Split-off statements: 0.
The private helper `augmentedResolutionComputation_naturality_aux` is fully proved.
The complete module passed the prescribed remote single-file compiler without warnings.

## No longer needed

None. No imports, nodes or modules were removed. Both declared proof dependencies,
`lem-weil-pbc-right-derived-plus-injective` and `def-weil-abstract-derived-category`,
are Mathlib leaves used by the proof; the existing unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

None. The supplied normalization and augmentation identities suffice exactly as stated.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
