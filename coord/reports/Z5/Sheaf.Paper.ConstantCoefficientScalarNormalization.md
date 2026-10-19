## What changed

Replaced the proof of `WeilConjectures.constantCoefficientRationalScalarIso_existsUnique`.
The recorded object formula of `sfRationalScalarExtension_existsUnique` identifies its
source with the rationalization of the integral scalar extension. Apply the rational
localization functor to `constantCoefficientConstructibleScalarIso`, transport its source
along this equality, and use `Iso.ext` to prove uniqueness from the required HEq of homs.
A proved private categorical helper handles this transport by equality induction.
All existing declarations, signatures, visibility, definitions and imports are preserved.
On resumption, compared the saved module against the current shared source and checked
its rational object formula against `SfRationalizationKaroubi`. The saved module compiles
cleanly through `lcompile.py` against the current server build (3.5 seconds, exit code 0).

## Proved and sorry left

Closed 1 of the item's 3 holes:
`WeilConjectures.constantCoefficientRationalScalarIso_existsUnique`.
Added 0 holes; no decomposition.

The following original holes remain, both attached to
`lem-weil-constant-coefficient-objects-constructible`:

- `WeilConjectures.constantCoefficientScalarUnit_existsUnique`: construction and
  uniqueness of the strict coefficient unit with its finite quotient normalizations.
  The existing completed scalar chain comparison supplies the quotient formulas, but
  still needs the ordinary scalar-extension identification on the regular module and
  the two-projection uniqueness argument for the prescribed strict cone.
- `WeilConjectures.constantCoefficientScalarUnit_isIso`: quasi-isomorphism of that unit.
  The surjective-tower theorem must be connected to the normalized scalar unit through
  the finite regular-module tensor identifications and the completed coefficient limit.

The rational proof uses the existing integral beta, whose definition still depends on
these two holes, and the existing rational scalar functor's object-formula theorem.
It therefore closes the rational normalization proof without claiming the integral
comparison or the entire target dependency closure is sorry-free.

## No longer needed

None. No imports removed and no nodes or modules pruned. Each existing public import
is used by the unchanged definitions and signatures. The proof follows the existing
rationalization step and leaves the unit route intact.

## Where the brief, the DAG or earlier work was wrong

The assigned source file was temporarily absent from the shared checkout when the
session began; it appeared during the initial reads. No mathematical discrepancy was
found in the rational normalization statement. Its uniqueness is categorical equality
of isomorphisms once the integral beta and the rational object formula are fixed.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
