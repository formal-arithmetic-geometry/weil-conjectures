## What changed

Implemented `refinementExchangeCoherence` with its original statement and all seven
clauses. The proof uses normalized proper/open vertical pasting, identity
normalization, the calculus cube, naturality, and cancellation. Parallel arrows
are equalized and their invertible comparisons cancelled. A common domination
then proves independence and the cocycle. Cancelling the second primed leg of
the two exchange squares proves naturality of the common-refinement ratio.

Added `Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence`. It proves the
unit and associativity equations for the existing section-normalized direct-image
compositors, and identity and pasting for their actual square mates. The proof
starts with restrictions of sections on the pro-etale site, passes through the
module adjunctions, termwise towers and exact derived localization, and then uses
formal adjunction conjugation and mate pasting. These equations apply to arbitrary
scheme maps and commuting squares; they assume neither properness nor finite origin.
The public predicate `DirectImageCoherence` states exactly these four equations;
its two mate-law definitions keep the full functor families explicit.

All existing public definitions and theorem signatures are preserved. No other
existing module is adapted. The auxiliary comparison representative is uniquely
determined by its proved equality to the original gamma; it introduces no new
operation or unproved choice. The new compositor representative is likewise
uniquely specified and proved equal to the canonical compositor with equality transport.
A private wrapper of the full square-mate family has a proved equality to the canonical
family. Generic equality-transfer lemmas keep these concrete constructions from
expanding during categorical substitutions. The last equation follows from a
cancellation lemma for natural-transformation squares and the defining equations
of the two common-refinement ratios. A private proof-independence lemma for
quasi-compactness arguments avoids expensive conversions between generated default
proofs; pullback objects and proofs are written explicitly where they enter that
cancellation. No private propositions or replacement compactification operations
are exported. A scoped unused-variable linter setting preserves the published
names of hypotheses inside the target's quantified statement.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.StrictTower.refinementExchangeCoherence`: one of one.
There are no remaining holes in the item and no holes added elsewhere.

The new theorem
`AlgebraicGeometry.ProEtale.StrictTower.strictTowerDirectImageCoherence` is also
proved completely, including the four normalization equations. All its private
helpers are proved. This delivery is a proof, with zero split-off holes.

Validation: a clean `lcompile.py --all` compiled the new API in 24.7 seconds and
the item in 7.5 seconds, with no warnings. The original target statement and the
bodies of both existing public comparison definitions were compared verbatim.
Both delivered Lean files contain zero proof placeholders.

The proof imports existing stated dependencies, including the proper/open calculus;
this report does not claim to close their holes.

## No longer needed

Removed the direct proof import `Sheaf.Paper.ProjectionCompactification`; the
compactification definitions remain available through the existing public imports.
The generic mate-pasting node is no longer a direct proof dependency of this item:
the new coherence node records the concrete normalization and its generic
mate-pasting dependency. Mate pasting remains needed in that new node.

Replaced the proof import `WeilConjectures.Compactification.CategoryBaseChange`
by `WeilConjectures.Compactification.Cofiltered`. Only its cofiltered-or-empty
instance is used: all primed compactifications and refinement squares are supplied
in the statement, so their existence and the base-change functor are not constructed.
The cofilteredness node remains a dependency for its cofilteredness declarations.

The second successive equalizer in the original common-refinement argument is
unnecessary. Equalizing and cancelling any pair of parallel arrows first permits
one common domination to compare ratios. The cofilteredness result is still used.
No whole module or DAG node is withdrawn. `StrictTowerCompositionPasting` remains
needed for `compositionF`, `compositionC`, and `compositionE`; its coherence theorem
is not applied.

## Where the brief, the DAG or earlier work was wrong

The refinement plan is mathematically sound. The references to canonical
compositors and generic mate pasting did not provide declarations for the unit and
pentagon equations of the particular section-normalized operations. The new node
supplies and proves those concrete equations, as well as identity and pasting for
`exchange`. These concern the operations alone and do not repackage refinement
coherence. Identity maps, empty schemes, zero coefficient rings and noncartesian
commuting squares require no exceptional hypotheses. The unit route is retained.

## New nodes

`lem-cbc-strict-tower-direct-image-coherence`: the canonical unit, associativity,
identity-mate and pasted-mate equations. Its source, complete proof in words,
four Mathlib searches and verbatim Lean statement are recorded in the node.
It has a complete Lean proof and no sorry.

Change record: `coord/changes/h4-refinement-exchange-proof-normalization.md`
records the local elaboration commands and private factorization change flagged by
preflight. There are no changes to existing public definitions or signatures.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
