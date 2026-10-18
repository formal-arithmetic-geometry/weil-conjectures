## What changed

Proved `WeilConjectures.FiniteFieldDatum.frobenius_square_cartesian` in
`Sheaf.SixFunctors.FrobeniusSquareCartesian`, with its statement unchanged.
The four inverse equations use `galoisMap_inverse`. Naturality is a direct
calculation on the two pullback projections using `galoisMap_projections` and
`Over.pullback_map_left`. Explicit isomorphisms assembled from the inverse
identities let `IsPullback.of_horiz_isIso` prove the model-morphism square.
The identity-base projection uses the standard IsIso instance; the final
structure square uses `AlgebraicGeometry.isPullback_baseChangeMap` after
unfolding the top map. Updated the existing node's proof and proof origin to
record these library applications. Imports, signatures and definitions are unchanged.

Validation: `lcompile.py` compiled the complete file without warnings in 3.7 s.
The proof works for unrestricted models, including empty and nonreduced schemes;
it uses only categorical pullbacks and the existing coefficient-action API.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.FiniteFieldDatum.frobenius_square_cartesian`
(node `lem-weil-frobenius-square-cartesian`).

Holes added: 0. Holes remaining in the delivered module: 0. No split-offs.
The proof uses the existing named dependency theorems `galoisMap_inverse` and
`galoisMap_projections` from `def-weil-frobenius-detailed`; their existing
proof obligations remain with that dependency module.

## No longer needed

None. No imports, nodes or modules were removed: all five original dependency
nodes still supply the datum, coefficient actions, spectra, schemes over the
base, and fibre-product universal property. The manual inverse computation for
the Cartesian comparison is already implemented by Mathlib's
`IsPullback.of_horiz_isIso`; the structure-square pasting argument is already
implemented by `isPullback_baseChangeMap`, so neither requires a new lemma.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The assigned theorem is already close to the
existing dependency API: the inverse equations and projection identities are
stated there, while the two generic Cartesian-square arguments are proved in
Mathlib and the source library. No statement repair or consumer adaptation was
needed. The unit's statement and proof steps are preserved.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
