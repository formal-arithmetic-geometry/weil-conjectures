## What changed

Completed the retirement item listed in `coord/retire-items.tsv`.
Withdrew `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound`, switched
its sole direct consumer `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart`
to the proved upstream twin, and redirected the existing node's Lean attachment.
The consumer's theorem statement and proof are unchanged. The upstream theorem differs
only by the explicit `.{u}` annotation on `SheafOfModules.overFunctor`, which elaborates
to the same type. The existing proof plan and dependencies remain accurate.

Change record: `coord/changes/P7-rhom-pseudo-part-bound-retirement.md`.

## Proved and sorry left

Original item holes: zero. Holes closed: zero. Holes added: zero. Holes remaining: zero.
`AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part_bound` already had a complete
proof; its existing upstream proof is now used by the unchanged parent proof.
This is a duplicate-module retirement, not a newly closed proof or a decomposition.
No new statements, axioms, definitions, or split-off obligations were introduced.
The original module, adapted direct consumer, and unchanged downstream theorem module
`Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent` each compiled cleanly using `lcompile.py`.
Delivery checks also compile the adapted consumer and check its declarations' axioms.

## No longer needed

Retired module: `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound`.
Removed its sole consumer import and replaced it with the upstream twin's import.
The withdrawn file's proof imports of `Sheaf.Paper.DerivedInternalHomRestrictOpen` and
`WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution` disappear with that
file; their mathematical roles remain in the upstream proof. No dependency node is
claimed unnecessary. The existing lower-bound node remains needed by its parent and
is preserved, attached to the upstream theorem. There is no bypass of the unit route.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item containing a hole, but this current item has
zero holes and is explicitly a retirement item. The retirement inventory labels the
pair DIFFERENT because the upstream statement writes the functor's universe explicitly;
comparison of the statements and successful compilation of the unchanged consumer proof
show that no mathematical API adaptation is required. Loogle and msearch grep found
no match; LeanFinder returned generic t-structure facts. Direct source inspection found
the exact proved upstream twin, so no new mathematical proof is needed.

The source `literature/stacks-project/perfect.tex`, lemma
`lemma-quasi-coherence-internal-hom` (Tag 0A6H), clause (1), was checked: the retained
upstream statement is the same local bounded-below component, with all hypotheses retained.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
