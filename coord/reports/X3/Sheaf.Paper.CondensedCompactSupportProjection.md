## What changed

Restored `lean/Sheaf/Paper/CondensedCompactSupportProjection.lean` from its current
quarantine archive, as required by its rework row. Preserved every public declaration,
definition, statement, public import, normalization, and Lean attachment.

Proved identity scalar exactness using `coefficientMap_id`, `Mod.extendScalarsId`,
and preservation of finite limits under natural isomorphism.

Proved shift compatibility of the actual compact-support coefficient projection.
Five proved private helper theorems detect comparison shift squares through their canonical
right-derived unit factorizations on K-injective representatives. They give the
right-derived natural, exact, and composition comparison shift laws used by the
restriction/direct-image square. The scalar adjunction shifts are exactly the
existing `condensedScalarShift` shifts; the open adjunctions use the existing
levelwise shifts. Expanding the mates and then the proper/open paste completes
the proof. The only added imports are proof-private:
`Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift` (with `import all` to
reuse its proved private canonical-unit calculation) and
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`.

Updated the existing node's proof, proof dependencies, and proof origin to record
these two completed arguments. No new statements or definition repairs were needed.
These helpers are registered as instances only inside the shift theorem proof.
The restored module compiles through `lcompile.py` against the current server snapshot.

## Proved and sorry left

Closed 2 of the archive's 9 holes, in namespace
`WeilConjectures.CompactSupportCondensedRealization`:

- `identityScalar_flat`.
- `condensedProjection_commShift`.

Added 0 holes and split off 0 statements. All five new private helpers are proved.
This is a partial proof delivery. The following 7 original named theorem holes
remain, all attached to node `def-pur-condensed-compact-support-projection` with
their original source and natural-language proof docstrings:

- `condensedProjection_comp`.
- `condensedProjection_id`.
- `fieldProperOpen_existsUnique`.
- `fieldRefinementApp_naturality`.
- `condensedProjection_refinement`.
- `fieldRefinement_id`.
- `fieldRefinement_comp`.

## No longer needed

None. No original import, declaration, module, statement dependency, or unit route
was removed. The original node had no proof dependencies; its one added proof
dependency supplies the already-proved canonical right-derived unit calculation.
The general ringed-refinement and finite-coefficient proper/open comparison modules
found by search use different coefficient/module presentations and are not imported
by these proofs.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it is quarantined, as recorded in
`coord/rework.tsv`; this is not a withdrawal. Its archive compiles against the
current server snapshot and retains the upstream-sync RefinementCategory import.
The definition node's original proof list was empty despite nine coherence and
refinement theorem holes in its module. The proved clauses above need no change
to their statements. The seven other original clauses remain unproved here; no
repackaged theorem or additional assumption was introduced to close them.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
