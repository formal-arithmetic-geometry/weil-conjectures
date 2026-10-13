## What changed

The existing theorem `CategoryTheory.filteredComplex_successor_cycles_cover_exists`
now applies the kernel universal property `HomologicalComplex.liftCycles` and its
composition equation. Its existing signature and both public imports are unchanged.
A proof-only import of `FilteredComplexSuccessorCyclesDifferentialZero` supplies
the outgoing-differential annihilation calculation. No definitions changed.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.filteredComplex_successor_cycles_cover_exists` (1 of 1 original holes).
Added one hole in
`CategoryTheory.filteredComplex_successor_cycles_differential_zero`, node
`lem-sp-filtered-complex-successor-cycles-differential-zero`.
This is a decomposition, not a net proof: one hole closed minus one hole added is zero.
The new theorem isolates the representative calculation; the original theorem supplies
the kernel factorization and its equation. Both declarations depend on `sorryAx`;
this delivery makes no claim of an axiom-clean final proof.

## No longer needed

No imports or modules pruned. The original direct proof dependencies
`def-sp-abelian`, `def-sp-filtration`, and `def-sp-filtered-complex-subquotients`
are removed from the parent's `proof_deps`: they remain statement dependencies and
are supplied transitively by the page-differential module. The parent's actual
proof dependencies are now the differential-zero lemma and page-differential data.
No unit realization was removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The first report called this a proof without identifying its zero net hole reduction.
The parent node was not updated to name the new intermediate theorem. The new
lemma's proof docstring omitted the image epimorphism, the target cokernel equation,
and cancellation. The second reading repairs these omissions.

An existing shorter formal route was found in
`filteredComplex_differential_representatives_cover`, at page r+1. Its source is
present in the repository, but its compiled module is missing from the current
local green-build cache. Importing it produced an object-file-missing compiler
error. It was not duplicated or compiled outside the authorized baseline. The
attempted route is recorded in sandbox scratchpad/representative-route.txt and
is not delivered; the new theorem retains a complete proof in words.

## New nodes

`lem-sp-filtered-complex-successor-cycles-differential-zero` states that the
successor inclusion followed by the quotient and outgoing differential vanishes.
Its source is Stacks Tag 012K, the displayed cycle and differential formulas.
It introduces no data construction or new definition.

## Second reading by A3

1. Compared the target module with the repository using diff. The sole existing
   theorem's signature is byte-for-byte unchanged, including hr, hZ and the
   prescribed composite. No definitions or target statements changed. Verdict: pass.
2. Compiled both modules locally. Checked both declarations using #print axioms in
   a scratch copy: only propext, Classical.choice, Quot.sound and sorryAx occur.
   The only source sorry is the named differential-zero theorem. No axiom, unsafe,
   opaque, implemented_by, extern or holed definition occurs. Verdict: valid
   decomposition, not an axiom-clean proof.
3. Read the cycle and differential formulas of https://stacks.math.columbia.edu/tag/012K.
   Successor representatives have differential in F^(p+r+1), killed in gr^(p+r).
   Their graded image covers successor cycles; cancellation therefore proves the
   new statement. Checked r=1, d=0, zero filtration steps and zero graded pieces:
   the same cokernel and image equations work and no extra hypothesis is needed.
   Searched with msearch leanfinder (filtered cochain representatives projecting
   to zero), loogle (HomologicalComplex.liftCycles_i), grep (representative cover,
   cokernel.condition and liftCycles_i), and rg on both library roots. Found the
   existing representative-cover theorem as the shorter route; it is not available
   in the compiled baseline. The new statement is the representative annihilation
   step, combined with an actual kernel-lift argument in the original module.
   Verdict: true, precisely needed; its docstring now gives the full argument.
4. Verified that liftCycles/liftCycles_i are the shortest generic kernel route.
   Tried removing the Mathlib import: cycles and iCycles became unavailable, so
   retained its public import because the signature needs them. The new import
   is proof-only. Read dag/units/sk-prop-av-pqf-finite.json: this item's node is
   not in its realized fields and no unit route is changed. No modules pruned;
   all removed direct proof-dependency nodes are listed above. Verdict: pass.
5. Read both node records and checked the new Lean signature against its recorded
   declaration. Corrected the parent proof, proof_deps and proof_origin to match
   the kernel reduction; expanded the new node's statement to include its full
   context and its proof to record the epimorphism and cokernel calculation.
   New-node source, search records, created, blueprint, chapter, unit and lean
   fields are present. Verdict: pass.

Changed by this reading: expanded the differential-zero docstring and node proof,
made its node statement self-contained, corrected the parent DAG route, and
corrected the report to account for the decomposition. The original kernel-lift
proof was retained.
