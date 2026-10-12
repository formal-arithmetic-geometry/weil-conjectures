## What changed

Replaced the original named hole in `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage` with the actual coproduct/induction and pullback proofs. The finite-union proof uses the existing `proper_coproduct_two` and `image_isClosedSubsetProperOver_of_universallyClosed` theorems; the inverse-image proof uses Mathlib's base-change instances and `Scheme.Pullback.range_fst`, then the existing closed-structure characterization. All existing declaration signatures, definitions, visibility, and the public import are unchanged.

Removed the first worker's two temporary conjunct modules and their two new nodes. Updated the existing target node's `proof`, `proof_deps`, and `proof_origin` to describe the actual proof. No new statements, definitions, modules, or change records are delivered.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Scheme.isClosedSubsetProperOver_union_preimage` (node `lem-weil-pbc-closed-subset-proper-over-base-union-preimage`). Added zero holes. There are no local `sorry`s left in the delivered module. This closes 1 of 1 original holes, with zero split off; it is not a decomposition into new admitted conjuncts.

The first worker's proposed holes `AlgebraicGeometry.Scheme.isClosedSubsetProperOver_union` and `AlgebraicGeometry.Scheme.isClosedSubsetProperOver_preimage` are removed, not delivered. Both arguments now live inside the original theorem. Existing imported admissions remain outside this item's scope. A scratch-copy `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`, and transitive `sorryAx`; consequently this is a local proof, not yet an admission-free target proof. Local compilation passes without warnings.

## No longer needed

Removed the redundant direct import `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`; the definition module already publicly imports it. Removed `lem-weil-pbc-reduced-induced-closed-subscheme` from the old `proof_deps`: the proof constructs the actual vanishing-ideal subschemes and uses Mathlib's range and closed-immersion facts, without applying this bundled theorem. Every other old proof dependency remains represented in the actual proof or its Mathlib instances and range corollary.

No established library module is claimed to be pruned from the targets' import closure: the reduced-structure module remains transitively imported. The two temporary new conjunct modules and nodes were removed before delivery. The three remaining private proof imports are used; proof-only imports added experimentally for Mathlib finite morphisms and pullback carriers were removed because the public definition import already supplies them.

## Where the brief, the DAG or earlier work was wrong

The first report described a conjunction decomposition as a proof while adding two holes. The new nodes had empty proof/search records and incorrect blueprint tags in their Lean docstrings, and the target node had not been updated. The reading replaced that decomposition with a real reduction to existing dependencies, removed the new nodes, and corrected the proof record. The source's finite-union and proper-preimage statements are true; no mathematical statement correction was necessary.

## Second reading by B2

1. Compared the delivered module against the repository with `diff`, and independently compared the original theorem signature byte for byte through `:= by`. Pass: no signature, definition, visibility, or public import changed; no accidental changes to another module. No change record is needed.
2. Compiled the first worker's three modules, then compiled the repaired single-module delivery without warnings. Scanned for forbidden declarations and local holes; none remain. Compiled a scratch copy with `#print axioms AlgebraicGeometry.Scheme.isClosedSubsetProperOver_union_preimage`: only the three permitted axioms and inherited `sorryAx`. Pass for a proof over existing open dependencies. The image theorem's existential closed subset is uniquely determined by its stated underlying image, and is used only through that equality; no arbitrary data is chosen from a mere-existence admission.
3. Read both proposed conjunct statements and their nodes. The statements were strictly smaller than the conjunction and true, but their records were incomplete. Checked the empty union, singleton/repeated subsets, empty schemes, empty inverse image, and identity proper map; the proof covers all without nonempty hypotheses. Searched with `msearch.py` using leanfinder (proper disjoint unions and inverse images), loogle (`Scheme.Pullback.range_fst`), and grep (`coprodDesc|range_fst|IsClosedSubsetProperOver`), plus `rg` on both Lean roots. Found the finite-coproduct instance and pullback-range corollary; no duplicate closed-subset theorem. Closed both arguments and removed all split-off statements and nodes. Pass: zero new statements to review.
4. Read Stacks' actual proofs of 0CYR and 0CYQ(3) in the available literature mirror. The repaired proof follows their coproduct/image and pullback/composition route, using the shortest available Mathlib facts for the subarguments. Removed redundant imports and listed the sole unused old dependency above. Read `dag/units/sk-thm-p1.json`, including `realized`; the item is not one of its fixed statement/step realizations, and no unit route or realization was changed. Pass.
5. Updated the existing node's proof steps and their dependency union to agree with the Lean proof, including the empty-family induction and the `range_fst` corollary. Retained its statement, statement dependencies, unit, chapter, Lean signature, and other metadata. Removed both incomplete new nodes rather than delivering them. Pass.

Second-reading changes: closed both proposed conjunct holes inside the original theorem; removed both new modules/nodes; pruned one redundant direct import and one unused proof dependency; corrected DAG proof metadata and this report. The original theorem's docstring and signature remain unchanged.
