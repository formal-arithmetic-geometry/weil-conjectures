## What changed

Retained the earlier sandbox item and ran its required initial delivery check.
Proved the original theorem, with no new statements left as `sorry`. The
statement and all six definitions are unchanged.
Private helpers prove scalar evaluation, local regularity in the constant ring
sheaf, vanishing of the scalar kernel on the flat algebra, flatness of the terms,
K-flatness, the cone-to-cokernel augmentation and its derived tensor comparison.
The complete proof compiled without warnings in 13.3 seconds, and again after
import cleanup in 22.5 seconds.

Scalar injectivity uses the existing local equational criterion, with one relation.
The augmentation uses Mathlib's canonical cone map from a short exact sequence.
The K-flatness criterion and fixed-factor tensor comparison are the existing
independent-coefficient interfaces. Import-direction checks passed for all four
new Sheaf proof imports. The copied DAG proof follows these arguments.

Change record: `coord/changes/U1-flat-scalar-resolution-imports.md` records the
public projection-mate import removal. The downstream tool confirms zero
downstream modules and no external uses of the declaration.

The argument also covers the zero ring and empty sites, using separatedness on
covering sieves. The finite factorization can have zero summands; its empty sum
is zero, as required. No enough-points hypothesis is introduced.

## Proved and sorry left

Proved: `SheafOfModules.flat_scalar_cyclic_resolution`
(node `lem-sfb-flat-scalar-cyclic-resolution`): one of one original holes closed.
Sorries left in this packet: none. Holes added: zero. No split.
All private helpers are proved and the full module compiles without warnings.
The existing imported fixed-factor tensor comparison remains its own stage-3 item.

## No longer needed

Removed imports: `Sheaf.Paper.ProjectionMateExact`,
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`,
`Mathlib.CategoryTheory.Sites.Sheafification`,
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, and
`Mathlib.Algebra.Homology.QuasiIso`.

Removed proof dependencies and obsolete tool-use approvals:
`lem-weil-pbc-ringed-projection-mate-exact` and
`lem-pc-bounded-above-flat-kflat-site`; the proof uses the fixed-factor tensor
comparison and independent-universe bounded-flat criterion instead.
`lem-weil-pbc-site-r-module-presheaf-sheafification-exact` is not needed as a
separate proof dependency: scalar regularity is proved directly by local
representatives and separation. `def-pc-acyclic-complex-modules` is not needed
separately: Mathlib's short-exact cone theorem supplies quasi-isomorphism.
No module is withdrawn and no parent route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The initial delivery check correctly returned `FAILED: nothing is proved` on
the unchanged earlier attempt. Fifteen direct remote compile requests and one
delivery check returned the busy-server response before elaboration. Spaced
retries continued until the server recovered. The complete proof then compiled
without warnings. The previous attempt's missing `ConstantSheaf.olean` is resolved.
The first final preflight rejected the change record's unsupported status word
`resolved`; this was corrected to `open` for the pending independent review.

The old plan's equal-universe bounded-flat theorem does not directly cover this
statement's independent universes. The existing independent-coefficient criterion
does. The old projection-mate theorem is unnecessary: the existing fixed-factor
comparison states precisely the required computation on unbounded complexes.
The two replacement criteria and the local-flat-relations theorem are general
ringed-site tools, used inside this unit's unchanged scalar-resolution argument.
No shared repository or launcher file was modified.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
