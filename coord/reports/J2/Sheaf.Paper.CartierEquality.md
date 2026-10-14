## What changed

The target module already contains the complete proof of `cartier_equality`; copied it into the sandbox and verified it compiles.

## Proved and sorry left

`cartier_equality` is proved. No `sorry` remain in the module and no new nodes were needed.

## No longer needed

None; the existing imports are used by the proof and retained.

## Where the brief, the DAG or earlier work was wrong

The repository module had already been repaired and landed, so this item required no additional source changes.

## Earlier second reading (a previous round; superseded)

The proof and statement were read against `lem-weil-pbc-cartier-equality`; the declaration is unchanged and compiles.

## Second reading by J2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only a proof comment was added.
2. Compiled `lean/Sheaf/Paper/CartierEquality.lean` with `lcompile.py`; it succeeds with no errors. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses the finite-extension zero transcendence-degree lemma for the final implication.
3. Checked the node statement and proof dependencies against the Lean proof. The theorem proves the stated finite-dimensionality, Cardinal equality, and finite-extension specialization without weakening or adding hypotheses. No split-off statements or nodes were needed, and no duplicate library theorem was introduced.
4. The proof follows the unit route: finite transcendence basis and complete-intersection fraction-field model, cotangent comparison, rank-nullity, and the transcendence-degree identification. Existing imports are used by the proof; no pruning was identified.
5. The unit's `realized` route and the node's `proof`, `proof_deps`, and `proof_origin` remain consistent with the proof. No DAG changes were needed.

Changed only the explanatory comment in the final finite-extension step; no mathematical or interface changes were made.
