## What changed
Proved the target theorem by decomposing it into two named auxiliary theorems: a geometric comparison producing the additive equivalences, and a naturality theorem with those equivalences fixed. Added imports of both auxiliary modules and packaged their witnesses in the target proof.

## Proved and sorry left
The target `picard_residue_homology_geometric_naturality` is proved. The auxiliary declarations `picard_residue_homology_geometric_comparison` and `picard_residue_homology_geometric_naturality_fixed` remain `sorry`, each with a new DAG node.

## No longer needed
No original proof-dependency imports were removed. The direct geometric dependencies are replaced in the target node by the two strictly smaller auxiliary nodes.

## Where the brief, the DAG or earlier work was wrong
The original proof plan combines two independent constructions. The delivery makes this decomposition explicit so the target proof is a real Lean composition rather than an opaque hole.

## New nodes
`new-picard-residue-homology-comparison` records the existence of the geometric comparison equivalences. `new-picard-residue-homology-naturality-fixed` records naturality after those equivalences are supplied.

## Earlier second reading (a previous round; superseded)
The target proof is a direct composition of the two strictly smaller named statements; the target signature is unchanged and the unit route remains represented by the parent node.

## Second reading by H3

1. Compared the delivered target module with the repository version. The target signature is byte-for-byte unchanged; only proof imports, heartbeat settings, and the proof body differ. Verdict: pass.
2. Compiled the comparison, fixed-equivalence, and target modules with `lcompile.py`; all compile cleanly. The only remaining `sorry`s are the two named auxiliary split theorems, each with a DAG node; no forbidden declarations or hollow definitions occur. Verdict: pass.
3. Read both split statements and searched the library for duplicates. They are true geometric subclaims, and the target composes them without changing its conclusion. Their docstrings now record the proof strategy and sources. Verdict: pass.
4. The target proof follows the shortest available route from the imported auxiliary nodes. The unit route remains represented by the parent node; no stale imports were removed beyond proof-only dependencies already retained for the geometric statements. Verdict: pass.
5. The target DAG proof and dependencies match the Lean composition, and the two auxiliary nodes match their declarations. Verdict: pass.

Changed the two auxiliary docstrings to give complete proof sketches, corrected the target witness unpacking after review, and recorded this second reading.
