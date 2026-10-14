## What changed

Applied the audited direct ordinary-pairing proof file for
`Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup`. The core and enclosing
external-cup theorems are complete and retain the corrected cover hypotheses
`hUc : iSup U = ⊤` and `hVc : iSup V = ⊤`. Retained the local irreducibility settings and proved
`moduleCup_congr` glue from the tested replacement.

The proof proceeds by forming the bidegree component, mapping cycles, using
homology naturality, applying the ordinary module Cech pairing with both cover
equalities, and finishing through the scalar/module external-cup comparison.
No target statement or definition is changed.

## Proved and sorry left

The declarations
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core` and
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup` contain complete
proofs with no local `sorry`. No new theorem or `sorry` is added. Existing
`sorryAx` dependencies are inherited from the imported ordinary and scalar
comparison primitives.

## No longer needed

The direct `Sheaf.Paper.ModuleCohomologyCupProduct` import was tested as unused
and removed because `exists_unique_moduleCupProduct` is already available through
the existing public imports. No DAG node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The uncovered core statement was correctly repaired upstream by restoring the
cover equalities. Without those hypotheses, comparison extensions outside the
union of the opens are unconstrained; the supplied P¹ example demonstrates the
failure. The current repository already contains that repaired statement and its
proof, so this delivery only rechecks the audited replacement.

## Second reading by F4

1. **Signatures and accidental changes — pass.** I diffed the delivered module
against the repository version. The two public theorem signatures and all existing
declaration types are unchanged; only proof text, authorship, and the unused
direct import were changed.
2. **Proof and axioms — pass.** `lcompile.py --all` compiles the module. A
scratch axiom probe reports only `propext`, `Classical.choice`, `Quot.sound`,
and inherited `sorryAx` from imported comparison primitives. There are no local
`sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
3. **Split statements and nodes — pass.** No new theorem or `sorry` is added,
so there are no new statements requiring nodes or duplicate-library checks.
4. **Shortest route and pruning — pass.** The proof keeps the ordinary module
Cech external-pairing route followed by scalar/module comparison. The direct
`ModuleCohomologyCupProduct` import was removed after a successful compile without
it; `exists_unique_moduleCupProduct` remains available transitively.
5. **DAG agreement — pass.** The core and wrapper declarations match their DAG
statements, including `hUc` and `hVc`, and the proof dependencies match the
declarations used. The module remains attached to unit `sk-prop-av-cube` and does
not bypass the unit route.

I changed the report and pruned the unused direct import from the item module.
