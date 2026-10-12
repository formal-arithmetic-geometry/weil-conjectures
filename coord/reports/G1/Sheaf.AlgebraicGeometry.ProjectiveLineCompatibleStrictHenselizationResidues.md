## What changed
Added a proof-only helper theorem isolating the residue-square compatibility step and imported it in the target module. The target theorem remains reduced to the existing strict henselization construction plus this helper.

## Proved and sorry left
`Etale.projectiveLine_compatibleStrictHenselizationResidues` is proved by applying the core construction and the residue-square lemma. `Etale.projectiveLine_compatibleStrictHenselizationResidues_core` remains `sorry` (node `compatible-strict-henselization-residues-core`). `Etale.compatibleStrictHenselization_residue_square` remains `sorry` (node `compatible-strict-henselization-residue-square`).

## No longer needed
No imports were removed. The attempted direct use of strict henselization functoriality is represented by the helper statement.

## Where the brief, the DAG or earlier work was wrong
The available functoriality theorem has a substantially more detailed interface than the target theorem, so the final residue equality cannot be obtained by direct application without an additional compatibility lemma.

## New nodes
`compatible-strict-henselization-residue-square` records the residue-square compatibility lemma introduced in the helper module. `compatible-strict-henselization-residues-core` records the core construction theorem in `Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore`.

## Second reading by G1

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof import and body differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; they compile without errors. The two remaining `sorry`s are named split theorems, with no sorry in definitions or unsafe declarations. Verdict: pass subject to the listed split nodes.
3. Checked the split statements against the target and DAG. The core theorem supplies the structural data, while the residue-square helper is used for the final conjunct. The helper is intentionally left as a named open statement because the available functoriality interface does not expose the required residue identification directly. Verdict: split is documented, though the helper requires the cited functoriality argument.
4. Read the proof route and imports. The target now uses the core construction and residue-square lemma; the old direct functoriality import is removed from the target. No old proof dependency can be pruned beyond that import. Verdict: pass.
5. Checked the node files and unit route. The target node's statement is unchanged, and the two new nodes record their declarations, sources, proof plans, and unit/chapter metadata. The unit route remains represented by the target node. Verdict: pass.

Changed during second reading: added this review record; no Lean statements or proofs were changed.
