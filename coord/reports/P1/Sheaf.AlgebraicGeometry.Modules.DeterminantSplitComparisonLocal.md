## What changed

Simplified the proof of
`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction` in
`Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal`: rewrite both occurrences
of the comparison equivalences using `hd`, then apply `hn`. This is the same elementary
substitution argument already recorded in `new-determinant-split-restriction`.
The declaration's signature, visibility, docstring and imports are unchanged.
The original and simplified modules each compiled cleanly through `lcompile.py`.

## Proved and sorry left

The sole declaration, `AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction`
(node `new-determinant-split-restriction`), remains fully proved. There were zero holes in the
checked-out module, zero holes are closed, zero holes are added, and zero holes remain.
This delivery is a proof simplification of an already repaired item, not new proof progress.

## No longer needed

None. The two public imports supply exterior sheaves and tensor-section infrastructure
(including the monoidal structure and short complexes) needed by the statement. There are no proof-dependency imports.
The node already has empty `proof_deps`; the proof route and the unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief says this module still contains `sorry`, but the supplied source has none.
The node records a reviewed proof landing dated 2026-10-14. The item is still listed in
`coord/repairs.txt` for an older false statement involving unconstrained lifts `c`; the current
statement instead assumes a natural linear family `dNatural` and pointwise equality `hd`.
That repair is already present and is preserved here. No statement correction or new node
is necessary. LeanFinder and local declaration search found no reason to replace the direct
substitution argument with an imported lemma.

The dry run refreshed the checkout to a newer base, whose proof was already shortened to
`rw [hd, hd]` and whose public imports are `ExteriorSheaf` and `TensorSection`. The final
sandbox preserves those current imports and uses explicit arguments in the two rewrites.

## Second reading by P1

1. Compared the delivered module with the repository version. The theorem signature,
visibility, docstring, and imports are byte-for-byte unchanged; only the proof term differs.
Verdict: pass.

2. Compiled the module with `lcompile.py` and searched the delivered files for `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`. Compilation succeeds and none
of those forbidden constructs occur. The proof has no open holes. Verdict: pass.

3. Checked the sole existing statement against node `new-determinant-split-restriction` and
the source route. The direct substitutions using `hd` are exactly the stated naturality
argument, with no added hypotheses or weakened conclusion; no split-off statement was added.
Verdict: pass.

4. Checked pruning and imports. Both public imports are required by the theorem's types, and
the proof has no additional dependency imports to remove. The unit route and its realized
nodes are unchanged. Verdict: pass.

5. Checked the DAG proof route and proof dependencies against the Lean proof. The node has
empty `proof_deps`, matching the local substitution proof, and no node metadata needs
editing. Verdict: pass.

Changed only the proof body to make both substitutions explicit (`rw [hd W hW y, hd Z
(hZW.trans hW)]`), preserving the theorem and all interfaces.
