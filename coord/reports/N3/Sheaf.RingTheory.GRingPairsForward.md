## What changed

Replaced the sorry in `Sheaf.RingTheory.GRingPairsForward.isGRing_pairsOfPrimes_forward` with a proof from existing declarations. First apply `isGRing_quotient hR q`, compose the regular localization map with the regular completion map, and take the resulting regular map's fibre at the zero prime of R/q. Both that prime's residue field and q.ResidueField are fraction fields of R/q. Their canonical algebra isomorphism induces the tensor isomorphism, with scalar compatibility checked by tensor induction. Transport geometric regularity; its Noetherian component supplies the other conjunct.

All new imports are proof-only: `Sheaf.RingTheory.QuotientGRing` and `Sheaf.RingTheory.GeometricRegularityFieldIso`. The existing statement, public import, and docstring are unchanged. Updated the existing forward node's proof, proof_deps, and proof_origin. No definition, signature, or statement changed.

## Proved and sorry left

Closed: `isGRing_pairsOfPrimes_forward` (the item's sole original hole).

Added holes: none. Sorries left in the delivered module: none. Removed both proposed split-off declarations, `isGRing_pairsOfPrimes_forward_noetherian` and `isGRing_pairsOfPrimes_forward_geometric`, and their new modules and node files. This is a proof of the item using existing dependencies, not a decomposition into new holes. Some imported dependencies remain open: a scratch-copy `#print axioms isGRing_pairsOfPrimes_forward` reports exactly `[propext, sorryAx, Classical.choice, Quot.sound]`.

## No longer needed

Removed direct proof-only imports `Sheaf.RingTheory.LocalCompletionQuotient` and `Sheaf.RingTheory.RegularThroughLocalization`. LocalCompletionQuotient remains used transitively by QuotientGRing; no claim is made that its module leaves the targets' import closure. The repository forward node had empty proof_deps, so there are no old listed dependencies omitted without accounting. The six declarations actually used now have matching proof_deps in that node.

The first worker's proposed GRingPairsForwardNoetherian and GRingPairsForwardGeometric imports, modules, and nodes were removed before delivery. Two provisional Mathlib imports were also removed after the smaller import set compiled. The remaining six proof imports each supply a declaration explicitly used by the proof.

## Where the brief, the DAG or earlier work was wrong

The first worker's conjunction decomposition added two holes for one closed hole, and its report called the conjuncts independent. In this library `Algebra.IsGeometricallyRegular` includes IsNoetherianRing, so its geometric helper was equivalent to the entire original target. Neither split was needed: the existing quotient G-ring permanence theorem supports a complete reduction. The first worker also left the original node's proof metadata unchanged. Both faults are repaired.

## Second reading by N3

1. Compared the delivered module with the repository using diff and checked the existing declaration through its `:= by`: its signature is byte-for-byte identical; its docstring, visibility, public import, and definitions are unchanged. Verdict: pass.
2. Compiled the final module with lcompile.py without errors or warnings. Checked forbidden constructs and sorries: none in the delivery. Compiled a scratch copy with #print axioms; only propext, Classical.choice, Quot.sound, and imported sorryAx occur. No arbitrary witness or data definition was introduced. Verdict: pass with already-open imported dependencies explicitly acknowledged.
3. Read both proposed component statements and tested their logic: the geometric component already implies the Noetherian one by definition. Searched Mathlib with msearch.py leanfinder, loogle, and grep using alternate queries, and searched upstream and lean/Sheaf with rg. Found the existing quotient G-ring and geometric-regularity transport declarations and used them. Removed every new split-off statement and node. Verdict: pass; none remain to review.
4. Read the original plan, all six previously planned imports, and dag/units/sk-thm-p1.json including realized. The new proof uses the existing quotient G-ring theorem (whose proof itself uses completion of a quotient), regular localization/composition, and a canonical fraction-field isomorphism; this is a shorter route below the unit level. No realized unit statement or step is bypassed or changed. Removed unused direct imports; recorded their transitive-use limitation above. Verdict: pass.
5. Updated only proof, proof_deps, and proof_origin of the existing forward node to match the final Lean proof. Checked each proof_deps node's declaration and module. No new nodes, statement changes, or change records remain. Verdict: pass.

Second reading replaced the conjunction restatement with a real proof from existing declarations, removed the two new holes and modules/nodes, pruned unused imports, and repaired DAG/report metadata.
