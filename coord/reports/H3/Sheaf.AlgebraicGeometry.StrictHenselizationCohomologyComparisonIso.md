## What changed

Repaired the return at delivery head 27625c9ae6f by reading the current item file,
which a02e6c2dfe9 created as an empty retired module. Reapplied the retained
original-model restoration to that current baseline. This restores an actual proved
theorem, rather than delivering the empty module or a rebase alone.

AlgebraicGeometry.Etale.isIso_strictHenselizationCohomologyComparison retains its
original small-colimit scheme, hypotheses, and canonical four-factor comparison.
The withdrawn specialized Leray definition is expanded using
exactGlobalSectionsLerayHomologyIso and the existing small-model exactness instance.
The proof combines three functor images of isomorphisms with strict-local base change
on global homology. All private helpers are proved. No adopted-source file changes.

The current node is used as the base, preserving all fields outside lean, proof,
proof_deps and proof_origin. Its original attachment and mathematical statement stay.
Change record: coord/changes/H3-strict-henselization-cohomology-comparison-restoration.md.

## Proved and sorry left

This is a restoration repair: proved 0 of 0 original textual sorries.
AlgebraicGeometry.Etale.isIso_strictHenselizationCohomologyComparison is fully proved.
No sorry remains, no hole is added, and no result is split off. The current empty
baseline also has zero holes, so no net hole reduction or target-closure progress
is claimed. The restored theorem compiles without warnings against the current
server snapshot (3.5 seconds).

## No longer needed

The restored proof does not import the retired
Sheaf.AlgebraicGeometry.StrictHenselizationRestriction. Its specialized Leray and
cohomology comparison definitions are not recreated. Instead the existing general
Leray API supplies the same canonical factor. The obsolete direct proof dependency
def-weil-pbc-strict-henselization-restriction is replaced by
def-weil-pbc-exact-global-sections-leray and
lem-weil-pbc-strict-henselization-scheme-sections-exact; the node's stmt_deps and
parents are preserved. No current module is withdrawn or claimed globally pruned.
The unit sk-thm-br has no realized statement or proof-step nodes; its route stays.

## Where the brief, the DAG or earlier work was wrong

The previous packet was based on an absent quarantined item at 777b431e1. The live
file is now an empty retired module, and coord/rework.tsv has no row for it. This
repair records the actual current file as Old and restores the original-model proof
in that file. The official WeilConjectures twin uses strictLocalization; replacing
this node's small-colimit statement by that theorem would change its objects.

The current unrestricted-stalk parent is also an empty retired module, rather than
a quarantined live importer. downstream.py and the source census find zero live
users of this item. Its parent DAG still cites the comparison node; no parent edge,
attachment or archive is deleted. The earlier compatibility probes are historical
checks of the original parent application and Leray specialization, not evidence
that the current empty parent provides a declaration.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
