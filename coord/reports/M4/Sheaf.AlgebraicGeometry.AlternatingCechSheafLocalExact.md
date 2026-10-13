## What changed

Closed the proof body of `AlgebraicGeometry.alternatingCechSheaf_restrict_local_exact`
without changing its signature or its existing docstring. The argument transports
sectionwise cocycle lifts through the natural sheafification units, proves presheaf
exactness through evaluations, reflects exactness through the faithful sheaf forgetful
functor, and constructs an isomorphism of the adjacent short complexes using
`extendXIso` and `extend_d_eq`.

Added `AlternatingCechPresheafLocalCocycles` for the strictly smaller sectionwise
signed-insertion calculation before sheafification or integer extension. Added and
fully proved `AlternatingCechPresheafTermsSheafification`: intersection is a composite
of continuous opens functors; hence each intersection presheaf is a sheaf, their
product is a sheaf, and the module-sheafification unit is invertible.

All new imports in the item are proof-only. No definition, existing statement,
visibility, or other group's module is changed. No witness is used to define data;
local existential witnesses occur only inside proofs.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.alternatingCechSheaf_restrict_local_exact`
(node `lem-pc-s3-alternating-cech-sheaf-local-exact`). Its complete combining proof
compiles, including the natural-degree and integer-degree transport.

New proved theorem: `AlgebraicGeometry.alternatingCechSheafPresheafTerms_unit_isIso`
(node `lem-pc-s3-alternating-cech-presheaf-terms-sheafification`), with no `sorry`.

Hole added and the only delivered `sorry`:
`AlgebraicGeometry.alternatingCechSheafPresheaf_local_cocycles`
(node `lem-pc-s3-alternating-cech-presheaf-local-cocycles`). It concerns a fixed test
open and natural degree in the explicitly constructed presheaf complex. Its docstring
and node give the signed-insertion primitive and both cases of the face calculation.

This closes one upper hole and adds one lower hole: a decomposition, not a net
hole-count proof. The sheafification argument and all categorical and integer-index
transport are proved. Edge cases checked mathematically: r=0 supplies no i; empty
opens have zero sections; if no increasing tuple of the middle degree exists that
term is zero; with r=1 every positive term is zero; no covering hypothesis or
degree-zero exactness assertion is introduced.

## No longer needed

No original import, node, or module is pruned. The sole original proof dependency,
`def-pc-s3-alternating-cech-sheaf-construction`, remains necessary. No splitting,
inner-inverse, positive-contraction, or global Čech-cohomology-comparison result is
used. The attempted new `ExtendHomology` import was removed: the proof only needs
`extendXIso` and `extend_d_eq` from the already imported extension construction.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. The original node combined the
sectionwise primitive, sheafification identification, sheaf exactness, and integer
extension into one proof step. The updated node now records the actual separation.
Existing all-tuple Čech exactness results do not directly apply to the strictly
increasing-tuple complex. Importing the downstream positive-contraction theorem
would introduce a cycle, so it was not used. LeanSearch was unavailable (Internal
Server Error); successful LeanFinder, Loogle, and grep searches are recorded.

The source proof was read at Stacks Tags 02FU and 01FM. The increasing-tuple
insertion calculation is the ordered version of the local contraction in 02FU;
all sheafification and categorical steps follow the original route. The unit's
statement and realized steps are preserved.

## New nodes

`lem-pc-s3-alternating-cech-presheaf-local-cocycles`, module
`Sheaf.AlgebraicGeometry.AlternatingCechPresheafLocalCocycles`: the remaining
sectionwise cocycle-primitive obligation, before sheafification and integer extension.

`lem-pc-s3-alternating-cech-presheaf-terms-sheafification`, module
`Sheaf.AlgebraicGeometry.AlternatingCechPresheafTermsSheafification`: the proved
invertibility of the canonical termwise sheafification unit. Both nodes inherit the
parent's chapter and unit, cite the same source, and record the actual searches.
There are no change records or forced adaptations.

## Second reading by M4

1. **Visible interfaces — pass.** Compared the item against the repository using
   `diff -u`: the sole existing public theorem's signature and docstring are byte
   for byte unchanged. No existing definition, visibility, or public import changes.
   The only new item imports are proof-only. The two new modules introduce named
   theorems, with construction imports public because their statements use them.
   No change record or forced adaptation is needed.
2. **Kernel checking — pass, with one declared lower obligation.** Compiled all
   three modules in import order using `lcompile.py --all`: no errors or warnings.
   Scanned every delivered Lean file: exactly one `sorry`, the whole proof of
   `AlgebraicGeometry.alternatingCechSheafPresheaf_local_cocycles`; no prohibited
   declarations, proof bypasses, or definitions with holes. A scratch-copy
   `#print axioms` check reports only `propext`, `Classical.choice`, and `Quot.sound`
   for `alternatingCechSheafPresheafTerms_unit_isIso`. The local-cocycles theorem
   and the item's theorem additionally use `sorryAx`, as expected. No data is
   defined by choosing an arbitrary witness of an unproved existence theorem.
3. **Split statement — pass.** Read the explicit presheaf terms and differential
   in `AlternatingCechSheafConstruction`, and independently read Stacks
   [02FU](https://stacks.math.columbia.edu/tag/02FU) and
   [01FM](https://stacks.math.columbia.edu/tag/01FM). Signed insertion gives the
   stated primitive without a covering assumption. Checked p=0, i first/interior/
   last in a tuple, r=0 (no i), r=1, empty V, and degrees with no increasing tuples.
   The remaining statement isolates the sectionwise face calculation and omits
   sheafification, exactness reflection, restriction, and integer transport; it
   does not restate the whole item. Its docstring and node contain a complete
   mathematical proof. Independent LeanFinder, Loogle, and grep searches through
   `msearch.py`, plus `rg` on both source roots, found no direct replacement.
   In particular `exactAt_cechComplex_of_bijective` and
   `exactAt_cechComplex_of_le` in `WeilConjectures.Topology.Sheaves.Cech` use
   all tuples, including repeats; applying them here would require an additional
   alternating-complex comparison. `HomologicalComplex.exact_iff_degreewise_exact`
   concerns complexes as objects, not presheaf evaluations. Neither is a shorter
   direct proof. Closing the remaining ordered face calculation is substantial
   further formalization, so no additional hole was closed in this reading.
4. **Top-down route and pruning — pass.** Read the proof's sheafification-unit
   transport, evaluation homology argument, faithful reflection, and three
   `extendXIso` maps with their differential compatibility. All added imports
   supply declarations used in these proofs. The original construction dependency
   remains used; the report's list of pruned original dependencies is complete
   (none). The unit `sk-thm-picard-f-representable` and its `realized` field remain
   unchanged; this item is below its statement and proof steps. The report
   correctly counts one upper hole closed and one lower hole added as a
   decomposition, with zero net reduction in holes.
5. **DAG agreement — pass after wording repair.** Compared the old and delivered
   parent node: only `proof`, `proof_deps`, and `proof_origin` change. The two new
   nodes contain the required source, searches, creation, blueprint, chapter,
   unit, and verbatim Lean-statement records. Their proof dependencies and the
   parent's dependencies agree with the argument and imports.

Changed only the new local-cocycles docstring and its node's proof text, plus this
report. Corrected the claim that insertion preserves the tuple intersection:
only its intersection with V is preserved. Expanded the two face-index cases and
sign exponents so the pending formalization can be reconstructed precisely.
No Lean proof body, statement, import, definition, or hole count changed.
