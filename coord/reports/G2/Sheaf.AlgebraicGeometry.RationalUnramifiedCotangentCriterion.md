## What changed

Proved `AlgebraicGeometry.rational_unramified_iff_cotangent_surjective` with its signature
unchanged. A proved private local-ring helper relates formal unramifiedness to cotangent
surjectivity for an essentially finite type local map whose composite with the target
residue map is surjective. The forward implication uses Mathlib's maximal-ideal criterion
and ideal-span induction; the reverse implication uses the exact differential sequence
and finite-module Nakayama. The scheme argument uses the existing proved theorem
`AlgebraicGeometry.FormallyUnramified.exists_neighbourhood_of_stalkMap` and Mathlib's stalk
and diagonal APIs. All existing public imports remain unchanged.

Updated the item's DAG proof and dependencies to describe this route. No statement,
definition, target, public interface, or consumer changes. A theorem-local unused-variable
linter setting retains the original hypotheses that the proof does not require.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.rational_unramified_iff_cotangent_surjective`
(node `lem-sc-rational-unramified-cotangent-criterion`).

Added zero holes. No `sorry` remains in the item or is added elsewhere. The private helper
`local_unramified_iff_cotangent_surjective` is proved in full. No split-off statements.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: its `IsUnramified`
definition is unnecessary because the unchanged statement already spells out locally
finite type and an open-immersion diagonal. The proof uses Mathlib's equivalence with
formal unramifiedness directly.

The item no longer directly needs these planned dependencies:

- `lem-weil-pbc-kahler-differentials-localization`;
- `lem-weil-pbc-unramified-ring-map-iff-unramified-affine`.

The existing proved stalk-neighbourhood theorem already packages the affine localization
and spreading argument. Removed the obsolete top-level tool-use approval for
`lem-weil-pbc-unramified-ring-map-iff-unramified-affine`; retained the Jacobi–Zariski one.
The Kähler-differential definition and Jacobi–Zariski node remain used via their Mathlib
matches. No additional Sheaf modules implementing those Mathlib leaves are imported.
No unit statement or unit proof step is bypassed (the unit record has no realization
attached to this supporting node).

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing plan's more elaborate kernel computation for
the differential map is unnecessary: the forward implication follows from Mathlib's
maximal-ideal equality for an essentially finite type unramified local algebra, while
surjectivity of the cotangent map alone makes the differential map zero in the reverse
implication. The closedness hypotheses, rationality at the target, and injectivity part
of rationality at the source are not needed by this proof; they are retained unchanged.

Validation: the complete module compiles through `lcompile.py` in 5.4 seconds.
The final delivery checks also verify its declaration axioms.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
