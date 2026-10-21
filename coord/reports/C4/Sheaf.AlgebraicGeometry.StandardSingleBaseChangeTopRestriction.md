## What changed

Restored `Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction` from the
quarantine path recorded in `coord/rework.tsv`. The source file was absent after
the cluster-restore rollback. Its full archived contents are restored verbatim,
including the public import, proof-only auxiliary import, theorem signature,
docstrings, options and complete proof. The quarantine archive remains intact.

The proof chooses the explicitly constructed
`standardSingleBaseChange_topRestriction_sourceIso p M` on the base, then applies
`standardSingleBaseChange_topRestriction_compatibility p M g e rfl` to obtain the
target isomorphism and its equation. In particular the source comparison is
constructed before derived pullback; no arbitrary source isomorphism is used.

The item compiled without warnings in 4.5 seconds using the prescribed compiler.
A separate `#print axioms` check returned exactly `propext`, `Classical.choice`
and `Quot.sound`. The unchanged archived direct consumer
`StandardSingleFlatCounitLocalizationPresentationData` compiled in 7.7 seconds
against the restored theorem. Verification copies of dependencies, the consumer
and the axiom probe are outside the delivered Lean tree.

The restoration record is
`coord/changes/C4-standard-single-base-change-top-restriction-restoration.md`.
No declaration or dependency source is adapted. The existing DAG attachment,
proof plan and unit route are preserved.

## Proved and sorry left

This is a zero-hole restoration repair: 0 direct holes before, 0 after; 0 holes
closed, 0 holes added, and 0 split off. The restored complete theorem is
`AlgebraicGeometry.standardSingleBaseChange_topRestriction_comparison`, attached
to `lem-pc-standard-single-base-change-top-restriction`. No `sorry` remains in the
item or is introduced elsewhere by this delivery. Its axiom closure contains
only the three permitted axioms.

## No longer needed

None. Both imports are needed: the public import supplies the comparison map
used in the statement, and the private import supplies the canonical source
isomorphism and its proved compatibility equation. No node, module, declaration
or import is withdrawn, and no dependency is claimed pruned. The existing
dependencies are retained, including those needed by quarantined parents.

## Where the brief, the DAG or earlier work was wrong

The assignment is a quarantine restoration rather than an unproved theorem:
the archived proof is complete. The initial compile encountered an import
conflict between cached `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap`
and its adopted `WeilConjectures` replacement. Compiling unchanged copies of
the current `OpenSingleCoefficientTransport` and
`StandardSingleBaseChangeTopRestrictionAux` resolved that verification conflict;
neither source is changed or delivered. A further standalone check with all
sandbox artifacts removed reproduced the published-artifact conflict. The
passing checks therefore explicitly use the freshly compiled unchanged
dependencies; delivery preflight performs the independent final check. The
restored theorem retains its exact
statement, including arbitrary modules and schemes, and introduces no flatness,
quasi-coherence, affineness or nonemptiness assumption. No global build or
comparator result is claimed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
