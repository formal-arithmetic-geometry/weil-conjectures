## What changed
The original signature of `AlgebraicGeometry.Scheme.root_split_cover_cyclic_charts`
is unchanged. Its proof obtains the cyclic chart model with equation φ(g), proves
regularity of the chosen affine etale base and its quotient and regular multiplication
by φ(g), and assembles the original existential conclusion.

Added proof-only imports of `RootSplitCoverCyclicChartModel` and
`EtaleRegularDivisorBaseChange`. The latter has a complete Lean proof using existing
`Algebra.isRegularRing_of_smooth`, flatness, and the quotient/tensor-product equivalence.
No definitions or existing signatures were changed.

## Proved and sorry left
Closed the one original hole, `AlgebraicGeometry.Scheme.root_split_cover_cyclic_charts`
(node `lem-sbc-root-split-cover-cyclic-charts`), by decomposition.
Added one hole, `AlgebraicGeometry.Scheme.root_split_cover_cyclic_chart_model`
(node `lem-sbc-root-split-cover-cyclic-chart-model`). This is the cyclic descent and
finite-presentation descent portion: it does not supply the three regularity properties
of the conclusion. The equation is constrained to be the image of the original g.

`AlgebraicGeometry.Scheme.etale_regular_divisor_base_change`
(node `lem-sbc-etale-regular-divisor-base-change`) is proved without a local sorry,
using the existing smooth regularity ascent theorem. No other sorry remains in the
files delivered. Net hole reduction is zero: this is a decomposition, not a completed
cyclic descent proof.

## No longer needed
None of the original imports or original dependency nodes was removed (the original
node had no proof dependencies). The regular-divisor helper needs no AdjoinRoot import. Second reading removed its
unused Mathlib.AlgebraicGeometry.Limits import and unused category namespace opens.

## Where the brief, the DAG or earlier work was wrong
The original three non-elementary proof steps had no stated dependency declarations.
The delivery separates the root model from the etale regularity bookkeeping, rather
than assuming that arbitrary regular chart data determine the given cover.

Edge cases checked against the new statements: n=0 is excluded; m=0 permits an empty
cover; away from the divisor the image of g is a unit and e=1 models split components;
a unit g gives zero divisor quotients; a zero base has no point y. No arbitrary data
are chosen from an unproved existence theorem inside any definition.

## New nodes
`lem-sbc-root-split-cover-cyclic-chart-model`: the remaining cyclic orbit classification
and descent argument, retaining the original divisor equation. Its docstring explains
connected cyclic descent at divisor points and the split cover case off the divisor.

`lem-sbc-etale-regular-divisor-base-change`: proved general preservation lemma, supplying
regularity of S, regular multiplication by φ(g), and regularity of S/(φ(g)). It depends
on `lem-weil-pbc-regular-ring-smooth-ascent`, already stated in the library. The parent
node's proof and proof dependencies now record these two components. No change record
is needed because no existing statement or definition was changed.

## Second reading by M1
1. I compared the delivered item module with the repository version. The theorem
   signature and all existing declarations are unchanged; only proof imports and body
   changed. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile cleanly.
   The only remaining `sorry` is the named theorem `root_split_cover_cyclic_chart_model`,
   listed above with its node and source proof. No definitions contain `sorry`, and no
   forbidden declarations occur. Verdict: pass subject to that split hole.
3. I checked both split statements, including empty index, unit divisor, and pointed cases.
   The helper is strictly weaker than the parent because regularity is supplied separately.
   Searches in both node files found no existing theorem duplicating either result. Verdict:
   pass.
4. The parent proof uses exactly the two helpers, with proof-only imports where appropriate.
   No old dependency or import became unnecessary. The unit's cyclic descent route is
   retained; the decomposition only separates regularity bookkeeping. Verdict: pass.
5. The DAG proof, proof_deps, and proof_origin fields match the Lean proof, and both new
   nodes carry statements, sources, searches, Lean records, chapter, and unit fields.
   Verdict: pass.

Second reading removed the unused Limits import and category namespace opens from the
regular-divisor helper, restored exact spacing before the parent proof, and added this
record. No existing statement or definition was changed. A scratch axiom probe showed
only propext, Classical.choice and Quot.sound for the regular-divisor helper; the parent
and model additionally use sorryAx, exactly as reported. The existing
root_split_cover_prescribed_cyclic_charts theorem was also inspected: it remains sorry
and requires a point on V(g), so does not close the model theorem. The unit realized
record is empty in the repository; this delivery does not bypass or alter its route.
