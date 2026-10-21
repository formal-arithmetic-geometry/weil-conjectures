## What changed

Proved `SheafOfModules.CommonLine.exists_coefficientNaturality` in
`Sheaf.Paper.CommonLinePositiveScalarPowers`, preserving its statement and every
existing public definition. The proof constructs the coefficient ring maps from
the tensor presentations, proves their ring laws by local lifting through the
module sheafification unit, and constructs semilinear maps on common lines and
all their powers. The extension map is the balanced scalar-extension lift. Its
comparison square is proved in degrees zero and one, then by tensor induction
and the prescribed successor formulas. All added helpers are private and proved.

Only the normalized binary-comparison module is needed as a proof import.
No adopted source-library file or downstream consumer is changed.
The proof-local command changes are documented in
`coord/changes/common-line-coefficient-naturality-proof.md`, as required by
the static visibility preflight.

## Proved and sorry left

Closed one of the two original holes:
`SheafOfModules.CommonLine.exists_coefficientNaturality`.

The original hole remains unchanged in
`SheafOfModules.CommonLine.exists_positiveScalarPowers`
(node `lem-pur-common-line-positive-scalar-powers`). It still asks for the initial
coefficient rings, common presentations and normalized power comparisons, with
the same-cover and generator formulas. Its full source and proof plan remain in
its original docstring and DAG node.

Added holes: none. Split-off statements: none. This is a proof of one original
hole, not a decomposition or a claim that the entire module is sorry-free.

## No longer needed

Removed unused private proof imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`;
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence`;
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`.

For coefficient naturality, ordinary tensor maps followed by module
sheafification, its local-surjectivity API, and the proved normalized binary
comparison suffice. No global generation of sheaf sections by pure tensors is
assumed. The removed modules' nodes remain dependencies of the original,
unproved initial-existence statement; this delivery does not withdraw them or
claim that they have left the target closure. No mathematical node is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The coefficient-naturality part needs no new
bilinear-extension existence assertion: its tensor and scalar-extension maps
can be constructed from the existing functorial and lift APIs. In the
multiplication proof, arbitrary sheaf sections must be lifted locally before
applying tensor induction; checking only global pure tensors would not suffice.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
