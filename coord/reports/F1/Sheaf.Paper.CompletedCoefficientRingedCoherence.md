## What changed

Completed the proof of `WeilConjectures.completedRingMap_slice` in
`Sheaf.Paper.CompletedCoefficientRingedCoherence`. Private helpers construct the
constant-ring and inverse-limit restriction comparisons, the geometric direct-image
comparison, its inverse-image mate, and the constant-section compatibility. The
completed structural-map equality follows by the existing joint projection uniqueness.
All existing public signatures and public imports are unchanged. The restriction
abbreviation now uses direct precomposition along `Over.map`; a private `rfl` theorem
proves equality with its original slice-equivalence composite. K5's
three previously completed proofs are preserved verbatim. The DAG's slice proof steps,
proof dependencies and proof origin now describe this direct argument.

Change record: `coord/changes/completed-coefficient-slice-proof.md`. The downstream
consumer is `Sheaf.Paper.OrdinaryImmersionChartComparison`, whose `chartRingIso`
chooses the first comparison from the unchanged theorem. No adaptation is needed.
The complete final module compiled cleanly in 25.8 seconds (`full26.log`).
Two earlier delivery attempts timed out during their initial compile and pushed
nothing. The final version replaces repeated expansion of the slice-equivalence
restriction composite by the definitionally equal direct restriction, factors
iterated-mate invertibility through a private generic lemma, and scopes
transparency settings before the unchanged public statement.

## Proved and sorry left

Closed 1 of the 1 initial holes: `WeilConjectures.completedRingMap_slice`, node
`lem-tw-completed-coefficient-ringed-coherence`. No `sorry` remains in this module
or any helper. Added holes: zero. Split-off holes: zero. The three previously proved
theorems are not counted as new work by F1.

## No longer needed

Removed the private import `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral` and its
proof dependency `lem-weil-pbc-localize-ringed-site-morphism`. The theorem's actual
geometric comparisons are obtained directly from the postcomposition/base-change
adjunctions and Mathlib's iterated-mate conjugation identity. The obsolete top-level
`tool_uses` entry for that node is removed. The module itself is not withdrawn: other
consumers may still use it. All other recorded dependencies remain. No module is withdrawn.

The candidate's extra imports of `Mathlib.CategoryTheory.Sites.CoverLifting`,
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory` and
`Mathlib.CategoryTheory.MorphismProperty.OverAdjunction` were removed as redundant:
the unchanged public imports already expose the needed APIs.

## Where the brief, the DAG or earlier work was wrong

The generic localization theorem is specialized to a single small-site universe,
whereas this statement has independent scheme and coefficient universes. The direct
mates construction proves the specified comparisons in those universes without
changing the mathematical statement or the unit route. The proof helpers use private
API lemmas for the projection calculation and completed-map equality. Private comparison constructions are made irreducible after
their API is proved, and helper-specific elaboration settings are scoped before the
unchanged public statement; this avoids expanding the chosen limit and mate data. The expensive restriction
abbreviation itself was replaced by direct precomposition, with its old construction
retained in the proved private equality `completedRestriction_slice`. No target
statement or definition changes mathematical meaning.
The restriction limit argument
uses preservation by precomposition; it never assumes arbitrary inverse images
preserve infinite limits.

The launcher resume changed the recorded reference clock: the earlier checkpoint
recorded start `1792751483`, while the resumed `.budget` records `1792768851.1796837`.
The worker did not edit budget metadata or use the reference clock to split a proof.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
