## What changed

The existing module `Sheaf.RingTheory.PowerSeriesRingSubfields` keeps its declaration
signature and all its public imports byte for byte. Its proof now derives all four
clauses from two strictly smaller coefficient-ring statements, with the actual
fraction-field and monotonicity arguments in the item itself. No definition or
existing statement changes; no change record or forced adaptation is needed.

New proof-only imports are `Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors`,
`Mathlib.LinearAlgebra.FreeModule.Finite.Basic`,
`Sheaf.RingTheory.PowerSeriesSubringFiniteBasis`, and
`Sheaf.RingTheory.PowerSeriesSubringIntersection`.
The finite-basis theorem provides a basis containing 1. Besides finiteness, this
lets a basis coordinate at 1 prove A intersect KJ = AJ by denominator cancellation.
The coefficient-subring intersection theorem supplies pth-power containment in AJ
and the polynomial pth root needed after clearing a denominator to its pth power.
The final union inclusion is proved directly from closure of the coefficient-field
generators, the coefficient conditions, and the quotient conditions.

The false unpublished `powerSeriesRingSubfieldsRemaining` and its new node were
removed, not weakened or retained as an axiom. Its replacement is the genuinely
smaller coefficient-ring intersection statement with the p-basis hypothesis.

## Proved and sorry left

Closed hole: `RingTheory.powerSeriesRingSubfields` (existing node
`lem-weil-pbc-power-series-ring-subfields`). Its body is a kernel-checked reduction,
not an axiom-free completed proof: the two intermediate declarations still have
`sorry`, so the item transitively uses `sorryAx`.

Added holes, both named theorems with complete sourced natural-language proofs:

- `RingTheory.powerSeriesSubringFiniteBasis`, node
  `lem-weil-pbc-power-series-subring-finite-basis`: finite coefficient-ring basis
  containing 1 (also used for saturation, not just the finite-module clause).
- `RingTheory.powerSeriesSubringIntersection`, node
  `lem-weil-pbc-power-series-subring-intersection`: for f in A, membership in all AJ
  is equivalent to being a pth power in A. This contains no fraction-field claim,
  no finite-module claim, and no union-inclusion claim.

This is a decomposition: one upper hole closed, two lower holes added, net -1
in the item/import closure relative to the original one-hole module. Zero of the
one original theorem is proved without `sorryAx`. It is not claimed as positive
ledger progress; the maintainer's pinned-baseline ledger determines global counts.
There is no `sorry` in a definition and no arbitrary object defined by choosing a
witness of an unproved existence theorem. The proof only eliminates existentials
inside a proposition. No forbidden axiom or unsafe feature is introduced.

## No longer needed

The first worker's proof-only `Mathlib.RingTheory.MvPowerSeries.Expand` import is
removed from the item: coefficient Frobenius belongs to the remaining coefficient
intersection proof, not the fraction-field reduction. The false unpublished
`Sheaf.RingTheory.PowerSeriesRingSubfieldsRemaining` module and its node are removed.
Unneeded `FractionRing`, `Finiteness.Defs`, and `Finset.Union` public imports were
removed from the new finite-basis module; the new coefficient-intersection module
also avoids them. No existing public import is removed.

Relative to the old parent's proof_deps:

- `def-weil-pbc-multivariate-power-series` and
  `def-weil-pbc-mv-polynomial-ring` move to the new coefficient nodes' statement
  and proof dependencies; their Mathlib types remain in the item signature.
- `def-weil-pbc-free-module` moves to the new coefficient nodes' dependencies;
  the actual basis is supplied by `powerSeriesSubringFiniteBasis`.
- `lem-weil-pbc-power-series-frobenius-coefficientwise` moves to the new
  coefficient-intersection node's proof dependencies. It remains needed there.
- `def-weil-pbc-localization-at-prime` is not used by this proof: the statement
  already supplies IsFractionRing, and Mathlib's injectivity and div_surjective
  provide the needed fraction-field facts directly.
- `lem-weil-pbc-power-series-domain`, `lem-weil-pbc-polynomial-ring-domain`, and
  `def-weil-finitely-generated-module` remain direct proof dependencies, through
  their Mathlib declarations/instances.

No existing Sheaf module is pruned from the target closure by this delivery.
The old parent proof-dependency modules were not imported by the repository's item;
removing a direct DAG edge does not mean those Mathlib modules are globally pruned.

## Where the brief, the DAG or earlier work was wrong

`powerSeriesRingSubfieldsRemaining` was false without the p-basis hypothesis.
Counterexample: p=2, k=F_2(s), I=N, t_i=s for every i, n=m=0, A and K identified
with k. For every finite J some i lies outside J, so kJ=AJ=KJ=k. Thus every stated
defining condition holds, but the intersection of all KJ is k, whereas K^2 is
F_2(s^2), a proper subfield (s is not a square). The unpublished false declaration
is removed; no statement weakening is used. The previous second-reading note
had missed this essential hypothesis and is superseded by this reading.

The first worker's two new nodes copied stale parent search/review metadata and
had placeholder proofs and non-self-contained statements. They are replaced by
accurate self-contained statements, detailed proof steps, and actual independently
recorded searches. The parent node previously retained the eight-step plan despite
the first worker's new proof; its proof, proof_deps, and proof_origin now record
the actual Lean reduction.

The new statements were checked at empty I, empty J, n=0, and m=0. Empty monomials
supply the basis vector 1; Frobenius roots remain uniquely determined in the
domain; only polynomial-column support must be finite. The field-span argument
uses finite-dimensional subrings on each element's finite set of generators and
does not wrongly impose finite power-series support.

The library and upstream searches found p-basis existence and differential
results, but neither coefficient-ring lemma. Mathlib hits concerning monomial
bases, perfection coefficients, and Frobenius expansion do not give these results.
The LeanSearch service returned Internal Server Error; that is recorded as
unavailable, not as evidence of absence. LeanFinder, Loogle, and Mathlib/source
rg searches were performed with different wording from the first worker.
The source route is confirmed against [Stacks Tag 07P5](https://stacks.math.columbia.edu/tag/07P5).

## New nodes

`lem-weil-pbc-power-series-subring-finite-basis` states the finite basis containing
1, isolating parent steps 3(b) and 4. Its docstring gives the exponent-division
construction, independence, spanning, finite enumeration, and degenerate cases.

`lem-weil-pbc-power-series-subring-intersection` states the coefficient-subring
intersection/pth-root equivalence in A, isolating parent steps 3(c) and 5. Its
docstring supplies the coefficient-field intersection argument and constructs
the polynomial root coefficientwise, respecting finite polynomial support.

No change records: all existing statements and definitions are unchanged.

## Second reading by M2

1. Compared the whole item with the repository using diff. PASS: the existing
   declaration signature and public imports are byte for byte unchanged. There
   are no definitions in the delivery. Only proofs, proof-only imports, new
   intermediate modules/nodes, proof metadata, and this report change.
2. Compiled every delivered module locally through lcompile.py. PASS: no errors
   or ordinary warnings, and exactly the two reported named theorem sorries.
   Axiom probes are checked for each declaration; the only dependencies are
   propext, Classical.choice, Quot.sound, and the expected transitive sorryAx.
   No axiom, unsafe, opaque, implemented_by, extern, or definition-level hole.
3. Checked both split-off statements, their degenerate cases, complete docstring
   proofs, and matching nodes. PASS after repair: the finite-basis statement is
   retained; the false remaining-conclusions theorem is removed and replaced by
   the smaller true coefficient-intersection lemma with the p-basis hypothesis.
   Independently searched Mathlib, the upstream library, and lean/Sheaf; no exact
   existing statement was found. Neither remaining hole merely restates the item.
4. Read the proof from the target downward and checked pruning. PASS: the actual
   quotient, saturation, denominator clearing, and union-inclusion proofs are in
   the item; smaller coefficient-ring arguments remain named. Removed unused
   proof imports and listed every old proof_deps edge that moved or was removed.
   Reviewed dag/units/sk-thm-p1.json realized: this item is below the unit-level
   nodes, and no realized unit statement or step is bypassed or changed. The
   source's coefficient/basis route is kept; no unit record edit is required.
5. Compared Lean declarations with all delivered node records. PASS after repair:
   new signatures agree verbatim; source, proof steps, proof_deps union, searches,
   created, chapter, unit, and lean records are present. The parent's proof and
   dependencies now follow the actual proof. No stale inherited reviewer verdicts
   are retained on the new nodes.

Second reading changed: removed the false missing-p-basis intermediate theorem;
added the genuine coefficient-subring intersection lemma; wrote the actual
fraction-field and monotonicity reduction; pruned unused imports; repaired both
new nodes and parent proof metadata; corrected the report's progress accounting.
