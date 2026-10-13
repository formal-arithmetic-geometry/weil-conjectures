## What changed

Proved `IsLocalRing.cohen_structure_power_series_surjection` in
`Sheaf.RingTheory.CohenStructurePowerSeriesSurjection`, with its signature and all public imports
unchanged. The characteristic-zero case uses the existing residue section; the positive case
uses the existing Cohen-ring existence and prescribed-residue lift. A local proved argument
constructs the power-series map from finite maximal-ideal generators and shows it is surjective
using Mathlib's `surjective_of_mk_map_comp_surjective`. Its key equality is
`Ideal.map φ (Ideal.span (Set.range X)) = maximalIdeal R`.

Added proof imports `Sheaf.RingTheory.CoefficientResidueSection`,
`Sheaf.RingTheory.CohenRingLiftToCompleteLocal`,
`Mathlib.RingTheory.AdicCompletion.Completeness`. Updated the existing node's proof, proof dependencies and
proof origin to match this route. No new modules, nodes, definitions, or statements.

The source was read at https://stacks.math.columbia.edu/tag/032A (the local literature file is
absent on this machine). The final paragraph directly uses the 0315 surjectivity argument now
implemented. The `sk-thm-p1` realized statement and steps are unchanged; this item is below them.

## Proved and sorry left

Closed 1 of 1 original holes:
`IsLocalRing.cohen_structure_power_series_surjection`
(node `lem-weil-pbc-cohen-structure-power-series-surjection`).
Added 0 holes. No `sorry` remains in the delivered module. This is a proof from existing
library declarations, not a decomposition into new holed statements; dependencies can still
rest on their existing holes. No claim is made that the whole target import closure is closed.

## No longer needed

Removed these direct proof imports (the second reader also removed the redundant newly added
`Mathlib.RingTheory.Finiteness.Defs` and `Mathlib.RingTheory.AdicCompletion.Functoriality`;
their APIs are already publicly available through Completeness):

- `Sheaf.RingTheory.ExistsCoefficientSubring`
  (`lem-weil-pbc-cohen-coefficient-ring-exists`): using the actual coefficient maps directly
  avoids constructing their image subrings.
- `Sheaf.RingTheory.CohenRingModPowFormallySmooth`
  (`lem-weil-pbc-cohen-ring-mod-pn-formally-smooth`): compatible lifts and their limit are
  already provided by `Sheaf.RingTheory.CohenRingLiftToCompleteLocal`
  (`lem-weil-pbc-cohen-ring-lift-complete-local`). The formal-smoothness result remains a
  transitive dependency of that lift; it is not pruned from this theorem's full closure.
- `Sheaf.RingTheory.FiniteOverCompleteRing`
  (`lem-weil-pbc-finite-over-complete-ring`): Mathlib's complete-source ring-map criterion
  (`lem-weil-pbc-complete-source-surjective-mod-ideal`) proves surjectivity directly without
  finite-module or quotient-module structures.

The original explicit `def-weil-pbc-adic-completion` dependency is no longer needed directly:
its inverse-limit construction is encapsulated in the two existing coefficient-map lemmas.
It remains needed transitively. Retained `Sheaf.RingTheory.CohenRingsExist`,
`Sheaf.RingTheory.PowerSeriesUniversalPropertyComplete`, and the power-series variables
completeness Mathlib leaf. These pruning claims concern this item's direct dependencies;
other target routes may still need the removed modules.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's plan was longer than necessary: existing stage-3
coefficient-map lemmas already implement its lifting steps, and Mathlib provides the direct
0315 surjectivity criterion that the source uses, avoiding the proposed 031D detour.
LeanFinder found no whole Cohen structure theorem. Loogle found the exact ring-map
surjectivity criterion; launcher grep and local searches confirmed its signature and the
finite-generating-family API. The empty family and both characteristic cases are allowed
by the unchanged signatures and the compiled proof. The two new imports pass the project's
import-direction check. No data definition chooses an arbitrary witness of an unproved theorem:
all existential choices occur within a theorem proof.

## Second reading by W3

1. Compared every delivered module and node with the repository version. The existing theorem
   signature is byte-for-byte identical, public imports and visibility are unchanged, and no
   definitions or statements were added or changed. Verdict: pass; no change record needed.
2. Compiled the sole delivered module locally without errors or warnings. Its body contains no
   sorry or forbidden declarations. A scratch copy with `#print axioms` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`: existing dependencies remain open,
   as the original report acknowledges. The finite-generating-family, ideal-map equality,
   coefficient residue lifts, and quotient-surjectivity argument were read line by line.
   All choices are local to this existential theorem proof, not data definitions. Verdict: pass.
3. No statements were split off and no new nodes were added, so there are no new holes or
   duplicate split statements to audit. Checked the unchanged statement in the empty-generator
   case (a field), residue characteristic zero, prime residue characteristic, and mixed
   characteristic; the proof covers each without an extra hypothesis. Verdict: pass.
4. Checked the direct [Stacks 032A](https://stacks.math.columbia.edu/tag/032A) proof and searched
   the library for Cohen presentations and the quotient-surjectivity criterion. The chosen
   route is the source's direct 0315 argument. The three old proof imports and the explicit
   adic-completion node removed from proof_deps are all listed above; transitive dependencies
   are not claimed pruned. The item's node is below the sk-thm-p1 realized statement/steps,
   all of which remain intact. Tested import removals: Finiteness.Defs and Functoriality are redundant (Completeness publicly
   imports the latter through Exactness), whereas Completeness is needed for the source precompleteness instance. Verdict: pass after pruning.
5. Checked proof/proof_deps/proof_origin against the Lean body and checked that proof_deps
   is exactly the union of the steps' uses. Only those allowed existing-node fields changed.
   The coefficient section, Cohen-ring existence/lift, power-series universal property,
   variables-completeness instance, and Mathlib surjectivity leaf all match. Verdict: pass.

Second-reading change: removed the unnecessary proof import
`Mathlib.RingTheory.Finiteness.Defs` and `Mathlib.RingTheory.AdicCompletion.Functoriality`,
and corrected the report's added-import list. No proof repair,
new hole, new statement, definition change, or further DAG change was needed.
