## What changed

Added a per-index geometric naturality theorem as a strictly smaller intermediate statement, then assembled its arrows by classical choice to prove the positive-family theorem. The empty-family theorem continues to reduce to the positive case.

## Proved and sorry left

Proved `picard_residue_homology_geometric_naturality_fixed` and
`picard_residue_homology_geometric_naturality_fixed_positive` from the per-index
component. The new theorem `picard_residue_homology_geometric_naturality_fixed_positive_per_index`
remains `sorry` as the geometric comparison step delegated to the next worker.

## No longer needed

None; all original imports remain needed by the per-index statement or assembly.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped at the positive-family theorem. The proof can be reduced to the strictly smaller fixed-index component and a genuine choice-based assembly.

## New nodes

`new-picard-residue-homology-geometric-naturality-fixed-per-index` records the fixed-index intermediate theorem and its delegated geometric proof.

## Second reading by K4

1. Compared the delivered family module with the repository version. Existing theorem statements are byte-for-byte unchanged; the proof-only replacement uses the new per-index theorem, and the new theorem is in its own module.
2. Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds with no errors. The only remaining `sorry` is the named per-index theorem, and it is documented and represented by its DAG node. No definitions, axioms, unsafe declarations, or forbidden implementation mechanisms were added.
3. Checked the split statement and searched the repository for duplicate declarations. The per-index statement is a strict component of the family existential and is exactly what the choice assembly needs; no existing theorem duplicates it. Its source, proof description, and Lean declaration agree in the new node.
4. The proof follows the shortest available route: classical choice assembles the per-index arrows, while the empty-family case is handled directly. All imports remain needed by the statements or delegated component, so none were pruned.
5. The unit route remains represented by the family theorem and its per-index decomposition; the node proof and proof dependencies match the written proof. No statement or definition change was made.

Changed the report only by recording this second reading; no Lean repair was needed.
