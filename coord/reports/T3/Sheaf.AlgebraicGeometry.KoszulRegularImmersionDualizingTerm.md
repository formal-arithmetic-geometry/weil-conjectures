## What changed

Proved `AlgebraicGeometry.koszulRegularImmersion_dualizing_term`, with its signature unchanged,
from one new local-rank lemma and existing exterior-power and pushforward results.
Added the module `Sheaf.AlgebraicGeometry.KoszulDualConormalRankStratum`, stating finite local
freeness of the restricted dual conormal with rank n. The original module adds only private
proof imports: that module, `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTopInvertible`,
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`, and
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.

The Lean proof obtains the local-rank instance, applies `exteriorSheaf_top_isInvertible`,
uses `IsInvertible.isQuasicoherent`, proves that the rank-fiber open inclusion is a closed
immersion using closedness of locally constant fibers, and applies
`isQuasicoherent_pushforward_of_isClosedImmersion`. Simplification of the nonnegative cast
identifies this pushforward with the defined term. Both modules compile without warnings.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.koszulRegularImmersion_dualizing_term`
(node `lem-sc-koszul-normal-determinant-term-qcoherent`).

Added one hole:
`AlgebraicGeometry.koszulRegularImmersion_dual_conormal_rank_stratum`
(node `lem-sc-koszul-dual-conormal-rank-stratum`) in
`Sheaf.AlgebraicGeometry.KoszulDualConormalRankStratum`.
This is a decomposition, with net zero holes, not a complete sorry-free proof. The new
lemma is only the first local algebra and rank-identification part of the original proof:
it has no exterior power, no pushforward and no quasi-coherence conclusion. Those remaining
parts are proved in the original module. No original-module sorry remains.

## No longer needed

No existing-module imports removed and no library modules pruned. The original public
imports define the unchanged statement's objects. The old direct proof dependency
`def-weil-pbc-koszul-regular-sequence` moves into the split lemma's local-algebra argument
and remains needed for both signatures; it is not pruned from the import closure.
`def-sc-locally-ranked-exterior-complex` remains a direct proof dependency.
The redundant explicit Quasicoherent import was removed from the new module only. The new proof reuses the existing top-exterior-power theorem and
closed-immersion pushforward result rather than adding holes for either operation.

## Where the brief, the DAG or earlier work was wrong

The original proof plan had only two definition dependencies despite requiring substantial
local algebra. An existing conormal-basis statement was found:
`ExteriorAlgebra.exists_koszul_conormal_basis` in `Sheaf.RingTheory.KoszulConormalBasis`.
The new lemma's plan uses this and `Scheme.Modules.affine_conormal_sections`, followed by
local dual bases, stalk finrank, and restriction of trivializations to the rank stratum.
No definition or existing signature is changed, and the unit route is retained.

The original referenced literature files are not present in this checkout. The cited Stacks
pages were read at https://stacks.math.columbia.edu/tag/0BQZ and
https://stacks.math.columbia.edu/tag/0BR0; the normal-sheaf local-freeness background is also
in https://stacks.math.columbia.edu/tag/0638 (regular immersions).

Edge cases of the new lemma: an empty rank stratum has a vacuous trivializing cover;
rank zero gives the empty local basis and the zero dual conormal; for a nonempty stratum
scheme stalk rings are nonzero, so finrank of a local basis really determines its size.
The subsequent existing exterior theorem includes rank zero and the empty scheme.

## New nodes

`lem-sc-koszul-dual-conormal-rank-stratum` states only finite local freeness of the dual
conormal restricted to the clopen rank-n stratum. It has the same immersion, regularity,
and rank hypotheses as the original, and concludes a strictly earlier step of the argument.
Its module contains one public theorem with one sorry, a source and full natural-language
proof. The node records actual LeanSearch (unavailable), Loogle and source-grep searches.
No change record is needed: existing interfaces remain unchanged.

## Second reading by T3

1. Compared the existing module with the repository using diff. Its declaration signature,
   docstring and visibility are byte for byte unchanged; only four private proof imports
   and the proof body differ. No existing definitions change and no change record is needed.
   Compared the existing node: only `proof`, `proof_deps`, and `proof_origin` change. PASS.
2. Compiled both modules in dependency order with lcompile.py, without errors or warnings.
   The item has no sorry; the new module has precisely the reported named theorem's whole
   proof sorry. No forbidden declarations or hollow definitions are added. Scratch copies
   with `#print axioms` show only propext, Classical.choice, Quot.sound and sorryAx, as
   expected for the open rank lemma and other imported open statements. PASS as decomposition.
3. Read the split lemma's statement, full docstring proof, node, the affine conormal sections
   theorem and the Koszul conormal basis theorem. The relation-to-cycle argument proves
   freeness over A/I; dual local frames preserve rank, and nonzero scheme stalk rings allow
   finrank to identify the frame cardinality with hr. Empty strata are vacuous, n=0 gives
   the zero conormal and its zero dual, and charts with unit ideal have empty inverse image.
   This is strictly the local-freeness part of the item, not its exterior or pushforward
   conclusion. Independently searched LeanFinder for dual conormal local freeness, Loogle
   for homObj_unit, and rg for conormal and dual locally-free declarations. Found the generic
   IsFiniteLocallyFree.dual tool but no exact rank-stratum theorem or immediate proof of
   conormal local freeness. The hole is sourced and matches its node. PASS.
4. Checked the shortest available route: existing exteriorSheaf_top_isInvertible and
   closed-immersion pushforward results close the remaining argument. All main proof imports
   supply a used theorem or instance. Added the split lemma's planned affine-conormal and
   Koszul-basis dependencies as plain proof imports; removed its redundant Quasicoherent
   import. Checked both old proof dependencies and corrected the pruning account above.
   Read dag/units/sk-thm-picard-duality.json: its realized fields are unchanged; the same
   local Koszul/conormal, determinant and clopen-pushforward route is retained. PASS.
5. Checked node statements against Lean, the new node's source, search records, creation,
   blueprint and Lean fields, and proof-dependency unions. Corrected the item's pushforward
   dependency from the indirect affine-morphism node to
   lem-pc-closed-immersion-coherent-cohomology, whose recorded declaration is the actual
   isQuasicoherent_pushforward_of_isClosedImmersion used. PASS after repair.

Second reading changed only the new module's imports, the item's DAG pushforward citation,
and the report's dependency/pruning account. No proof body or signature needed repair.
The single upper hole is closed with one strictly simpler hole added: net zero, decomposition.
