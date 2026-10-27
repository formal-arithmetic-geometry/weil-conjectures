## What changed

Proved `AlgebraicGeometry.Scheme.hasEtaleCoordinateCalculus` in the assigned module.
All existing public declarations, their signatures, and the public imports are unchanged.
The only added declarations are proved private helpers inside the assigned module.

The affine-coordinate differential basis is constructed by transporting Mathlib's
polynomial basis through formally étale differential base change. The polynomial map
is identified explicitly with the given morphism's affine section map, including its
scalar map. The dual basis gives the coordinate derivations. The universal derivation
and basis extensionality prove evaluation bijectivity, uniqueness, the differential
formula, commutation, and naturality under algebra homomorphisms.

Stalk differential bases are obtained from an affine neighbourhood by localization and
differential base change. Duality and naturality then give the single compatible stalk
family, without invoking the separate completion-and-localization theorem. Formal
partial differentiation is restricted to k and compared by coordinate evaluation on
both sections and stalks. List induction proves every iterated comparison.

Updated the assigned DAG node's proof, proof dependencies, proof origin and obsolete
tool approval to match this argument. No other existing module or node is changed.
The proof uses no factorial inverses and treats zero coordinates and empty affine opens
uniformly. Basis choices are uniquely determined by their prescribed vectors; no
arbitrary mathematical object is extracted from an existence-only assumption.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.hasEtaleCoordinateCalculus`
(node `lem-trf-etale-coordinate-derivations-jacobian`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered module: 0.
No split-off statements or new modules are delivered. Every private helper is proved.
The complete module compiled on the project server in 8.7 seconds.
`#print axioms hasEtaleCoordinateCalculus` reports exactly `propext`,
`Classical.choice` and `Quot.sound`.

## No longer needed

Removed proof imports:

- `WeilConjectures.RingTheory.Derivation.CompletionAndLocalization`: stalk derivations
  are dual to localized differential bases, so neither the completion result nor its
  separate localization-extension result is needed.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: the required spectrum/global-section
  isomorphisms are already supplied by the existing public affine-space import.

Removed from this node's proof dependencies:

- `lem-weil-pbc-derivation-extends`: replaced by localized differential bases and
  coordinate-evaluation uniqueness; also removed its obsolete `tool_uses` entry.
- `lem-a1-etale-open-restriction`: the affine section map is étale directly by
  `Scheme.Hom.etale_appLE`; no restricted scheme morphism is constructed.
- `lem-weil-pbc-morphism-into-affine-scheme`: the polynomial section-map identification
  is proved explicitly using `AffineSpace.SpecIso_hom_appTop`, constants and variables.

These are dependency removals for this item. No source-library declaration or module
is deleted, and no claim is made that these dependencies have no other consumers.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The earlier proof plan's separate extension-of-derivations
step is unnecessary: the same formally étale differential comparison used on affine
opens also supplies the stalk basis after localization. This proves compatibility and
Taylor comparison on all germs directly from coordinate evaluation. The original
finite-type and quasi-compact hypotheses are retained verbatim, although this proof
does not need them. The unit route is preserved.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
