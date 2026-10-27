## What changed

Proved `AlgebraicGeometry.Proj.commonDegreeTwistInvertible` using the given homogeneous
cover directly. Positive powers replace the cover by degree-e elements. Their integer
powers give local free generators, and pointwise multiplication extends uniquely through
the proved sheaf tensor universal property on Proj, then transports it to V using the
proved restriction-tensor comparison. Local bijectivity proves the binary maps are
isomorphisms. A recursion starting with the restricted unit isomorphism constructs the
canonical tensor-power isomorphisms and proves both required section formulas.

All new definitions and helpers are private to the item. The multiplication definition
chooses from an existence-and-uniqueness theorem specifying its action on every local pure
tensor, so this choice determines the morphism. No arbitrary existence witness is used.
The existing theorem signature and public imports are unchanged. The DAG proof follows
the actual construction. The consumer search finds `Sheaf.TraceFormula.ProjQcOpenTwistAmple`
as the only external declaration user; its call and all hypotheses and conclusions remain
unchanged. The unit route is preserved. The full module compiles cleanly through
`lcompile.py` in 46.7 seconds, with no warnings. Scope-command change record:
`coord/changes/H9-proj-common-degree-proof-scope.md`.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.Proj.commonDegreeTwistInvertible`
(node `lem-trf-proj-common-degree-twist-invertible`). Added no holes; no `sorry` remains
in the working file. The complete module compiles cleanly; all new private helpers are
proved, with no split-off statements. Actual item hole count: 0 (originally 1).

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.ProjTwistSectionBasicOpen` and
`WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties`. The proof does not need
`lem-trf-proj-twist-section-basic-open`, `lem-weil-pbc-proj-standard-open-inclusion`, or
the finite-subcover step through `def-weil-pbc-quasi-compact-scheme`: the cover is already
an input. Removed the obsolete standard-open-inclusion entry in `tool_uses`. These are
local dependency removals; this delivery does not withdraw any module or declaration.

## Where the brief, the DAG or earlier work was wrong

`twistSectionBasicOpen` states nonvanishing-locus and basis assertions, not the
invertibility and multiplication assertions attributed to it in the old proof plan.
The proof instead constructs these assertions directly on the degree-e standard-open
cover, as in Stacks 01MU. The supplied cover also makes the old finite-subcover step
unnecessary. The node's reference to lemma-where-invertible as Tag 01MS is a citation
typo: the source is Tag 01MU. The unit route is preserved.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
