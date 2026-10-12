## What changed

Proved `LocalizedModule.proj_away_degreeZero_exact_pair` in
`Sheaf.Algebra.Module.ProjAwayDegreeZeroExactPair`, preserving its full signature.
Added the proof-only import `Sheaf.Algebra.Module.AwayDegreeZeroLift`.
The proof identifies the chart maps with ordinary localized maps, uses Mathlib
localization exactness, and applies the existing proved homogeneous lifting theorem
for kernel preimages and for the conditional surjectivity assertion. The conditional
injectivity assertion follows from ordinary localized injectivity.
Updated the item's DAG proof and proof dependencies to match this route.

Searches: LeanFinder returned `IsLocalizedModule.map_exact` and related ordinary
localization results, but no degree-zero module result. Loogle confirmed
`IsLocalizedModule.map_exact`. Grep and repository search found the existing proved
`LocalizedModule.away_degreeZero_lift` and its use in
`Sheaf.Algebra.Module.ProjAwayDegreeZeroExact`. The latter needs both endpoint
hypotheses, so it cannot directly prove this exact-pair statement.

## Proved and sorry left

Closed the single original hole:
`LocalizedModule.proj_away_degreeZero_exact_pair`
(node `lem-sc-p1-away-degreezero-exact-pair`).
No sorries remain in the item, and no new holes or statements were added.
The dependency `LocalizedModule.away_degreeZero_lift` already has a complete proof.
This is a proof, not a decomposition.
Local compilation completed without errors or warnings. The launcher snapshot initially
lacked the object for the recently landed lifting theorem; an unchanged sandbox copy
of that existing module was compiled for local validation and removed from the
delivery source set. Its cached sandbox object is used by the local compile.

## No longer needed

No existing imports were removed. All four public imports occur in the unchanged
statement, and `Mathlib.Algebra.Module.LocalizedModule.Exact` is used by the proof.
The existing dependency `lem-sc-p1-localization-short-exact` remains used through
Mathlib's `IsLocalizedModule.map_exact`, `map_injective`, and `map_surjective`.
No existing DAG node or module is pruned.
The planned construction and internality proof of an integer grading on each
localized module is unnecessary: the existing
`lem-sc-p1-away-degreezero-lift` gives exactly the homogeneous preimages needed,
by clearing denominators and projecting in the original modules.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The initial DAG omitted the now-existing homogeneous
lifting node from its proof dependencies. The revised proof records that dependency
instead of rebuilding a localized internal grading. Exactness is proved before,
and independently of, either endpoint implication. The unit record has no realized
steps bypassed by this route. The zero-polynomial case is covered by the existing
lifting theorem; the commuting-square and Mathlib arguments apply uniformly.

## Second reading by V1

1. Compared the sole delivered Lean module with the repository using `diff -u`.
   Verdict: pass. The existing declaration's signature, docstring, and definitions
   are byte for byte unchanged; only its proof and one plain proof-only import differ.
   There are no statement changes or change records required.
2. Compiled the module with `lcompile.py`, without errors or warnings. A scratch copy
   with `#print axioms LocalizedModule.proj_away_degreeZero_exact_pair` compiled and
   printed exactly `propext`, `Classical.choice`, and `Quot.sound`. Scanned the delivered
   file for sorries and forbidden declarations/attributes: none. Verdict: pass.
3. No statements were split off and no new declarations or nodes were added.
   Read the existing `away_degreeZero_lift` proof: it constructs its homogeneous
   preimage by decomposition, handles f=0 by subsingleton localization, and uses
   no arbitrary witness from an unproved existence theorem. Zero modules, zero maps,
   zero numerators and f=0 introduce no missing case. Verdict: pass.
4. Read the proof from exactness down to the two conditional endpoint conclusions.
   Both commuting squares follow from the prescribed fraction formulas; exactness
   uses ordinary localization and a homogeneous lift without endpoint assumptions.
   Searched the library for degree-zero exactness and lifting statements, and inspected
   Mathlib's localized exactness and endpoint lemmas. The existing short-exact chart
   theorem requires both endpoint assumptions; `graded_localization_exact` remains
   unproved and uses a different homogeneous-piece API. No shorter proved route was
   found. All statement imports and both proof imports are needed. The old dependency
   on ordinary localization exactness is retained, so the pruning list is complete.
   Inspected `dag/units/sk-thm-picard-duality.json`: no realized statement or step
   is bypassed or changed. Verdict: pass.
5. Compared the node with its repository version. Only `proof`, `proof_deps` and
   `proof_origin` changed. They describe exactly the ordinary-localization transport
   and the two uses of `lem-sc-p1-away-degreezero-lift`; the existing Mathlib-match
   node records all three localization lemmas used. Verdict: pass.

Second reading changed only this report, adding the independent review and axiom
verification. The Lean proof and DAG record needed no repair. Holes closed: one,
`LocalizedModule.proj_away_degreeZero_exact_pair`; holes added: zero.
