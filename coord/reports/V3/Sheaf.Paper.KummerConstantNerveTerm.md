## What changed

Filled the three theorem proofs in `Sheaf.Paper.KummerConstantNerveTerm`.
The underived and derived uniqueness theorems use their existing canonical
composites as witnesses and Mathlib's `CategoryTheory.Iso.ext` for uniqueness.
The structural-map equation follows from
`coefficientParameterProjectionCommutes`, associativity, and the supplied
commuting-square equality. All signatures, definitions, and imports are preserved.

## Proved and sorry left

Closed 3 of 3 holes, all attached to
`def-sfb-kummer-constant-nerve-term`:

- `AlgebraicGeometry.ProEtale.CondensedRing.kummerSquareModuleIso_existsUnique`
- `AlgebraicGeometry.ProEtale.CondensedRing.kummerSquareDerivedModuleIso_existsUnique`
- `AlgebraicGeometry.ProEtale.CondensedRing.kummerPuncturedParameter_over`

Zero holes remain in the item; zero holes added and zero statements split off.

## No longer needed

None. The existing public import `Sheaf.Paper.KummerNerveTransport` is still
required for the statement and the canonical composites. No dependency node or
module is pruned; all three statement dependencies remain needed. The existing
DAG proof is empty; the completed proofs implement the arguments already given
in the theorem docstrings without changing the route or adding dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The historical rework row is retained; the
current item source is present and supplies the original declarations.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
