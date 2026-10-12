## What changed

Added proof-only imports for two strictly simpler intermediate statements and reduced the
cokernel-closure proof to the canonical ambient cokernel plus its universal isomorphism.
The canonical cokernel and isomorphism-invariance statements remain named `sorry` theorems.

## Proved and sorry left

The target `AlgebraicGeometry.coherentFormalModules_closedUnderCokernels` is proved by
combining the two intermediate declarations with `IsColimit.coconePointUniqueUpToIso`.
The new theorem `AlgebraicGeometry.coherentFormalModules_canonicalCokernel_isCoherent`
remains `sorry` (node `lem-weil-pbc-coherent-formal-cokernel-canonical`). The new theorem
`AlgebraicGeometry.coherentFormalModules_of_iso` remains `sorry` (node
`lem-weil-pbc-coherent-formal-iso-invariant`).

## No longer needed

None of the target's stated proof dependencies were removed; the proof uses the formal
module definition and generic cokernel machinery through the two intermediate modules.

## Where the brief, the DAG or earlier work was wrong

The direct termwise proof planned by the DAG is not available in the current Lean library
within this item. The reduction exposes its two independent geometric obligations as
strictly smaller named statements while preserving the target statement and unit route.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading; the target reduction and both intermediate
statements have been compiled together with `lcompile.py --all`.

## New nodes

`lem-weil-pbc-coherent-formal-cokernel-canonical` — canonical ambient cokernel coherence;
module `Sheaf.AlgebraicGeometry.CoherentFormalModulesCokernelCanonical`.

`lem-weil-pbc-coherent-formal-iso-invariant` — invariance under inverse-system isomorphism;
module `Sheaf.AlgebraicGeometry.CoherentFormalModulesIsoInvariant`.

## Second reading by J1

1. **No accidental visible changes.** Compared the delivered closure module with the
repository version. The target theorem signature is byte-for-byte unchanged. The two
additional modules contain only the newly split named statements. Verdict: pass.

2. **Proof and declarations.** Compiled all three modules with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all`; they compile cleanly. The only
remaining `sorry`s are the two named split-off theorems, and neither occurs in a
definition or an anonymous declaration. The closure theorem is proved using the
canonical cokernel theorem and `IsColimit.coconePointUniqueUpToIso`; no forbidden
constructs were added. Verdict: pass.

3. **Split-off statements.** Checked both statements against the formal-module
definition and the cokernel argument: canonical cokernel coherence and invariance under
inverse-system isomorphism are true, strictly simpler obligations, and each has a
source, proof sketch, and matching DAG node. Searches found no existing declarations
with either statement. Verdict: pass.

4. **Pruning and route.** The target keeps the unit route through the canonical cokernel
and transport isomorphism. The canonical module imports the four proof-dependency
modules recorded by its node; the closure module uses only the two split-off modules.
No dependency was removed. Verdict: pass.

5. **DAG agreement.** The closure node's proof and `proof_deps` match the Lean proof;
the two new nodes record their statements, sources, modules, and split status. Verdict:
pass.

Changed the canonical module to include its recorded proof-only imports and added this
second-reading report.
