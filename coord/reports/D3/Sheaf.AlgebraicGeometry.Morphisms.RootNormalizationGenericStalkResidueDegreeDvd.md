## What changed
Added the proof-only import `Sheaf.AlgebraicGeometry.Morphisms.NormalizationResidueDegreeDvdCore` and reduced the target theorem to that abstract arithmetic normalization statement. Added the core module with the remaining Stacks Tag 09EB argument as one named theorem.

## Proved and sorry left
The target `AlgebraicGeometry.Scheme.root_normalization_generic_stalk_residue_degree_dvd` is proved by a real application after unfolding its local definitions. The new theorem `AlgebraicGeometry.Scheme.normalization_residue_degree_dvd_core` remains `sorry`; it is the strictly more general finite-etale normalization/DVR residue-degree calculation and has node `lem-sbc-root-normalization-generic-stalk-residue-degree-dvd-core`.

## No longer needed
The proof-only import `Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange` was removed because
the target proof uses only the abstract core theorem. The core module's unused public import of
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor` was also removed. The target's direct
geometric construction is no longer unfolded in the arithmetic argument; it is supplied only
through the abstract core theorem.

## Where the brief, the DAG or earlier work was wrong
The DAG omitted the abstract finite-etale normalization/DVR calculation needed to make the target proof compositional. It has been added as a new node.

## New nodes
`lem-sbc-root-normalization-generic-stalk-residue-degree-dvd-core` in `dag/nodes/sec-smooth-base-change/`; its Lean declaration is in `lean/Sheaf/AlgebraicGeometry/Morphisms/NormalizationResidueDegreeDvdCore.lean`.

## Second reading by D3
1. I compared the delivered target module with the repository version. Existing theorem
signatures are unchanged; the only target change is the proof and a proof-only import.
Verdict: passed.
2. I compiled both delivered modules with `lcompile.py`. The target has no `sorry`; the only
remaining `sorry` is the named core theorem, with no hollow definition, axiom, unsafe, opaque,
extern, or implemented_by declaration. Verdict: passed.
3. I searched the library and ran the required Mathlib searches. The split-off core statement is
strictly more general than the target and records its Stacks Tag 09EB source and node; no existing
declaration duplicates it. Verdict: passed.
4. I checked the proof route and imports. The target applies the core arithmetic result after
unfolding its local objects, and unused normalization-stalk and torsor imports were pruned.
Verdict: passed.
5. I checked the core node against the Lean declaration and retained the unit and chapter route;
the node's proof dependencies and `proof_origin` match the stated split theorem. Verdict: passed.

I changed only the target proof, added the core theorem module and node, pruned two unused imports,
and added this second-reading record.
