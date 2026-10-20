## What changed

Repaired and restored the three-module quarantined rework cluster rooted at
Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts.
The helper module loses two orphaned scoped option commands before its closing
namespace. Its generated module comment is wrapped, and the standard private-module
linter setting documents that it intentionally contains private helpers only.
Every helper signature and every definition is preserved.

The private proof finite_components_lift replaces a costly change/congrArg/trans
calculation over nested pullbacks with direct rewrites by hM, Category.assoc and hj,
followed by simp only [θ, Category.assoc]. This proves the same first-projection
identity without the expensive definitional-equality search identified in the
previous repair's profiling. No file or proof is split and no limit is raised.

Restored Sheaf.AlgebraicGeometry.GrothendieckHypercoverSectionColimit with its two
duplicate import-all lines redirected to one import-all of the extracted helper
module. Its public imports and all declaration signatures and bodies are preserved.
Restored Sheaf.AlgebraicGeometry.GrothendieckHypercoverLimitGeneration from the
current quarantined source verbatim.

Repair of the return at delivery head 070ca68e01: checked the current rework rows,
claim and return, and compared the retained limit-generation file with the current
quarantined source. The live lean/ file is absent; the quarantine file and retained
file are byte-for-byte equal (SHA-256
d32aedff61813594a0a5bbba8d6cc46debe865d993623428f29f2f6fdc7e1f9d).
Copied that current source into the sandbox again, retaining the substantive helper
and section-colimit repairs above. Thus this packet preserves the current proof
rather than overwriting a newer version. The delivery tool rebases the whole packet
on its freshly fetched sheaf-dag base.

Validation on this retry: lcompile.py --all compiled all three modules in import
order with no warnings, exit code 0, in 12.6 s, 4.9 s and 3.7 s respectively.
The earlier counterfactual compile of the original section-colimit consumer against
the repaired helper failed at line 32 with Unknown identifier truncated_terms_qcqs,
confirming that redirecting the private-helper import is required.

Change record: coord/changes/finite-hypercover-descent-parts-extraction.md.

## Proved and sorry left

Assigned zero-hole rework repair: 0 holes closed, 0 added, 0 remaining in the item
or either restored consumer; 0 split off. Every existing proof remains complete.
No new theorem is introduced. The upstream finite_hypercover_descent_objects,
finite_hypercover_descent_morphisms and finite_hypercover_descent_equalities are
outside this repair; their source module is untouched.

## No longer needed

Removed the two duplicate import-all lines for
WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts from the
section-colimit consumer, replacing them with one import-all of the extracted
helper module. Its existing public import remains. No mathematical dependency,
node, declaration or module is pruned; the proof route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ because the sync quarantined it. Its input
is the archive named in coord/rework.tsv, rather than an empty or withdrawn module.
The archive has zero sorries. Its extraction left scoped options without the theorem
that formerly followed them and a consumer importing private helpers from their
former module. These are the actual defects repaired here.

The current return reports a concurrent edit to limit-generation after the previous
delivery base e0d550965. The current archive matches the retained proof exactly;
taking that source and regenerating the delivery against current sheaf-dag resolves
the stale-base conflict without deleting the archive or changing its theorem.
No target, definition, statement, DAG proof route or upstream source file changes.
Both consumer nodes retain their Lean attachments and dependencies, so no node edits
are needed. Independent review is the maintainer's delivery review.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
