## What changed

Proved `AlgebraicGeometry.ProEtale.reductionOrientation` in
`Sheaf.SecSmoothPurity.ReductionOrientation` by specializing the existing proved theorem
`AlgebraicGeometry.Etale.FiniteSmoothPurity.normalizedOrientation_scalar` to
`N = M = ℓ ^ n`, with `dvd_refl`. Added its module as a private proof import.
The supplied orientations, normalization witnesses, geometry and coefficient-line
comparison are passed unchanged. The Noetherian and quasi-compact instances are
constructed from the existing finite-type hypotheses, using the same expressions as
the theorem signature. All public imports, signatures and definitions are unchanged.
Updated the item's node proof and proof dependencies to this shorter route.

Validation: `lcompile.py` compiled the proof successfully (exit 0, 5.4 s).
The import-direction check accepts the new private import. The general theorem
handles arbitrary finite coefficient maps, including non-flat maps, rank zero,
zero rings and empty schemes; this application adds no assumption.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtale.reductionOrientation`
(node `lem-sp-reduction-orientation`). No holes remain in the item; no holes were
added or split off. The imported general theorem has a complete Lean proof from
its stated lower dependencies; those pre-existing dependency holes are unchanged.

## No longer needed

No existing imports were removed: both public imports are required by the theorem's
statement and remain verbatim. No module is withdrawn.

The former proof dependencies `det-sp-finite-general-ring`,
`det-sp-reduction-exceptional`, `det-sp-reduction-direct-image`,
`det-sp-scalar-extension-functor`, and `def-pur-finite-smooth-coefficient-arrows`
are not separate proof steps of this specialization. They are replaced in the
item's `proof_deps` by `lem-sp-finite-normalized-orientation-scalar`.
This is pruning of the planned common-prime-ring/cocycle proof, not a claim that
these modules leave the targets' import closure: some remain statement dependencies
or dependencies of the imported general theorem. In particular `FiniteGeneralRing`
and `FiniteSmoothCoefficientArrows` still supply the statement's canonical data.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned common-prime-ring argument is unnecessary:
the general finite-ring normalized-orientation theorem landed on 2026-10-27 and
already proves the required equation at equal exponents. Its proof uses the same
source's diagonal, normalized Rees specialization and vector-integration squares.
The unit `sk-lem-sp-reduction` has no realized steps assigned to this node, and its
coefficient-comparison route is preserved. No chapter or unit record changes.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
