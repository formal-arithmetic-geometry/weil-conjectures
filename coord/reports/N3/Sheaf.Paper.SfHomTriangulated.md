## What changed

Repaired `AlgebraicGeometry.Etale.sf_internalHom_triangulated` by replacing the local
intermediate ring-sheaf binding with a direct `simpa only` specialization of
`CategoryTheory.RingedHomUniverses.ringedInternalHom_exact` at universes
`(u + 1, u, u + 1, w)`. The theorem statement, imports, and the existing
independent-universe interface remain unchanged. The sandbox module compiles together
with its interface dependency.

## Proved and sorry left

The existing proof hole of `AlgebraicGeometry.Etale.sf_internalHom_triangulated` is
closed. The module contains zero `sorry`s after this repair. No new theorem or
intermediate hole was added.

## No longer needed

None. The independent-universe exactness interface remains required by the proof, and
no imported module or DAG dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The earlier red-build delivery generalized the existing restriction theorem in place,
which changed universe inference for downstream modules. That route caused failures in
four consumers. The current independent-universe interface is a separate theorem and
its direct specialization avoids those failures; this repair keeps that route and does
not alter the restriction theorem.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
