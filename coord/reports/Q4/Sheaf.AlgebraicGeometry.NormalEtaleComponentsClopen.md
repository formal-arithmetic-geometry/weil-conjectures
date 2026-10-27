## What changed

Filled `AlgebraicGeometry.normal_etale_components_clopen` in the item module, preserving
its statement and public imports. Normality of the source stalks comes from the proved
source-library étale normality theorem. The proved local connectedness and irreducibility
results identify connected and irreducible components without a finite decomposition.
Private helpers transport the enlarged-universe strict-henselization presentation to
algebras over `ULift A`, where the existing locality, small-filtered index and normal-colimit
results apply. Updated the node proof and dependencies to follow this route.
The open-command record is `coord/changes/normal-etale-components-clopen-open-commands.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.normal_etale_components_clopen`
(node `lem-a1-normal-etale-components-clopen`), 1 of 1 original holes.
Holes added: zero. Holes remaining in this delivery: zero.
Every private helper has a complete proof. Existing dependency theorems keep their proof status.

## No longer needed

Removed unused proof imports:

- `WeilConjectures.RingTheory.EtaleNormalRing`
- `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.StructureSheaf`
- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.AlgebraicGeometry.FunctionField`
- `Mathlib.RingTheory.Localization.LocalizationLocalization`

The affine decomposition route through `rem-pc-regular-normal` and its module
`Sheaf.AlgebraicGeometry.RegularNormalDecomposition` is unnecessary: the proved source-library
results make each connected component an irreducible clopen open subscheme directly.
Its top-level tool approval is removed. No global pairwise-disjointness argument is needed.
The restriction/injectivity result `lem-sc-components-open-injection` and the separate covering
result `lem-sc-irreducible-components-cover` are unnecessary for this maximality argument.
The finite-presentation/pointwise criterion detour (`def-sbc-locally-finite-presentation`,
`lem-weil-pbc-lft-pointwise-criterion`) is unnecessary because Mathlib already supplies the
locally finite type instance. The strict spectrum uses `PrimeSpectrum.irreducibleSpace`
directly, without `def-pc-integral-scheme` or `lem-weil-pbc-spec-domain-stalks-function-field`.
No source-library declaration or module is removed, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original statement is correct, including empty sources and sources that are not
quasi-compact. The strict-henselization step cited single-universe results while this item
allows the residue closure and colimit ring in a larger common universe. A private change
of base along `ULift A ≃+* A`, including the induced residue-field isomorphism, reconciles
these interfaces. No public statement or definition repair is needed.
The component plan is longer than the existing proved source-library argument.
Sources read: Stacks 0357, 0BQ3 and 06DI; unit `sk-p-real-rankin` remains unchanged.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
