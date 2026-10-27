## What changed

Proved `WeilConjectures.finiteHomEtaleClosed_existsUnique` in
`Sheaf.Paper.EtaleFiniteCoefficientHomArrow` by constructing the published closed
record and proving uniqueness from its monoidal and adjunction fields. The
remaining evaluation-naturality field is a proposition. The construction uses
the existing proved `finiteHomEvaluation_naturality` and the uniquely normalized
Koszul braiding.

Three generic definitions share the same internal Hom, right adjunction and
closed normalization before specializing the coefficient category. The existing
etale definitions now call these definitions. Their old and new bodies are
definitionally equal. The signed-total inclusion retains its body and replaces
its unused abelian hypothesis by preadditivity. This avoids a costly comparison
of inherited additive structures. Public imports and target statements stay
unchanged. All new private helpers are proved.

Change record:
`coord/changes/q5-etale-finite-hom-shared-closed-normalization.md`.

## Proved and sorry left

Closed 1 of 2 original holes:
`WeilConjectures.finiteHomEtaleClosed_existsUnique`, attached to
`def-sf-etale-finite-coefficient-hom-arrow`.

The sole unchanged original hole is
`WeilConjectures.finiteHomEtaleRepresentativeData_existsUnique`, attached to the
same node. Added 0 holes; split off 0 statements. No hole is placed in a
definition. The chosen closed record is fixed uniquely by the stated
normalization, rather than selected from unconstrained existence.

## No longer needed

None. All original public imports support the retained definitions and
statements. No dependency, module or unit step is removed. The definition node
has no planned proof dependencies; its statement dependencies and unit route
remain intact.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The tensor-inclusion helper assumed an
abelian category even though only its preadditive tensor data are used. Its
weaker structural requirement retains the actual summand inclusion.

Launcher LeanFinder, Loogle and grep searches found no existing normalization
uniqueness theorem for this record. Record extensionality and function
extensionality suffice. The representative-data hole was also proved in
experiments, but the combined specialized conversion checks exceeded the
per-file limit. Those experiments and all profiling settings are excluded.

The delivered closed-normalization candidate compiled cleanly in 47.9 seconds.
The actual delivery module and the unchanged K-flat presentation consumer also
compiled in a set against the sandbox build. A combined reflexivity audit of
the former definition bodies exceeded the compile stop while expanding derived
structures; no failed audit theorem is included. The separate axiom audit passed in 5.9 seconds:
`finiteHomEtaleClosed_existsUnique` depends only on `propext`, `Classical.choice`
and `Quot.sound`. The delivery preflight performs the final compilation and
axiom checks. The old and new bodies in the change record permit direct independent
comparison. No compile limit is raised and no file or proof is
split for performance.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
