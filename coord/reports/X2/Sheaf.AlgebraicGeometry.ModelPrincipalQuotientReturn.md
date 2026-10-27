## What changed

Proved `AlgebraicGeometry.modelPrincipalQuotientReturn` in the assigned module without
changing its signature or public imports. A proved private helper constructs the
localized principal-quotient base-change equivalence and verifies the fraction formula.
The main proof transfers flatness along this equivalence, proves finite presentation,
constructs the basic-open isomorphism and a quotient point over the specified point,
and identifies the actual composite with the affine spectrum map followed by the
base chart's open immersion. Mathlib's affine morphism-property criteria then prove
flatness and local finite presentation. Only the assigned Lean module and its own
DAG node are changed.

Added the proof import `Mathlib.RingTheory.Localization.Away.AdjoinRoot` for finite
presentation of a principal localization. Updated the node's proof and proof dependencies
to match the constructed argument.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.modelPrincipalQuotientReturn`
(node `lem-trf-model-principal-quotient-return`): 1 of 1 holes proved. The private
helper `principalQuotientBaseChange` is also fully proved. Added zero holes and split
off zero statements. No `sorry` remains in the delivery. The module compiled in 11.4
seconds, and `#print axioms AlgebraicGeometry.modelPrincipalQuotientReturn` reported
only `propext`, `Classical.choice`, and `Quot.sound`. The diagnostic command was removed
after this check; the delivery tool checks the final module again.

## No longer needed

Removed the proof imports `Mathlib.AlgebraicGeometry.ResidueField`,
`Mathlib.RingTheory.TensorProduct.Maps`, `Mathlib.RingTheory.MvPolynomial.Localization`,
and `Mathlib.RingTheory.Flat.Localization`. The proof works with affine chart ranges
and prime ideals directly, uses the tensor-quotient equivalence API, uses the existing
finite-presentation API for a principal localization, and applies the affine
morphism-property criteria.

The expanded stalk argument is unnecessary. Removed these dependencies from this node:

- `lem-weil-pbc-affine-open-stalk-localization`;
- `lem-weil-pbc-spec-map-stalk-localization`;
- `lem-weil-pbc-localization-flat`;
- `lem-weil-pbc-flat-ring-map-comp`;
- `lem-weil-pbc-flat-over-localization`.

No existing module is withdrawn. The unit's statement and realized proof steps are
unchanged. The other nodes of the original plan remain represented by the algebra,
localization, quotient, finite-presentation, and chart arguments.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The Mathlib match recorded for the
quotient-spectrum image lemma names `PrimeSpectrum.range_comap_of_surjective`, but
the usable declaration in the installed library is `_root_.range_comap_of_surjective`.
The implementation uses that declaration. Mathlib's affine criteria also make the
plan's explicit stalk-localization proof unnecessary. The original theorem signature
and all public imports were compared verbatim with the repository source.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
