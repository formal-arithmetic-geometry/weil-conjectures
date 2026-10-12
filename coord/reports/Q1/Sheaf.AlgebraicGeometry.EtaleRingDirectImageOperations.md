## What changed

Proved `AlgebraicGeometry.etaleRingDirectImageOperations` in
`Sheaf.AlgebraicGeometry.EtaleRingDirectImageOperations`, with its signature,
visibility and original imports unchanged. Added the fully proved private helper
`transportSectionOperations` for equality transport of bundled internal ring
operations. No new public declarations, nodes, dependencies or adaptations.

The proof implements the node's three steps. Apply the F operation assumptions
to G(X), then eliminate the bundled-ring equality G ⋙ F = identity to identify
the inverse G carrier maps with those operation-preserving maps. On the V site,
cancel the inverse carrier map to obtain the forward operation formulas.
For the sectionwise pushforward's inverse product comparison, evaluate its two
projection equations and use pair extensionality. Evaluate the RF operation
identities on pairs or on the singleton section. Combine these equations with
the U-site operation formulas to prove all four clauses.
For constants, the U formula holds for every terminal section, so no separate
calculation of the terminal comparison is needed.

Validated the recovered sandbox proof by single-file compilation without warnings
and by the delivery dry run, including the declaration axiom probe. The dry run
printed OK; the independent second reading remains for the second reader.
All edits are confined to the sandbox; nothing was pushed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.etaleRingDirectImageOperations`
(node `lem-weil-pbc-etale-ring-direct-image-operations`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.
The private `transportSectionOperations` helper is fully proved by equality
elimination. This is a proof, not a decomposition into new unproved statements.

## No longer needed

None. No imports were added or removed. The original node has no proof
dependencies, and the proof needs no additional project modules or nodes.
The statement's ring-core and lifted-ring nodes remain statement dependencies;
their theorems are not used as proof premises here.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The three-step plan is sufficient.
The previous compile.log records failed inverse-comparison and equality-transport
attempts; the recovered Lean file already contains their repairs. Recompilation
confirms the repaired file is clean. The product calculation now uses
`Iso.inv_comp_eq` and the two projection equations, avoiding unfolding the
unexposed generic categorical inverse.
Negation assumptions are not needed for the four requested equations.
The proof does not assume nonzero rings, inhabited ring sections beyond their
ring structure, points of either scheme, or nonempty sites. Equality transport
preserves the complete bundled ring structure, including in the zero-ring case.
No signature or visibility changes; no forced adaptations.

## Second reading by Q1

1. Compared the delivered module with the repository version. The theorem signature, visibility, imports, and existing declarations are unchanged; only the proof and a private helper were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. No `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` occurs, and an axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. The private equality-transport helper is fully proved and introduces no split-off statement or node. The target theorem is exactly the existing node statement, with no weakened hypotheses or conclusions. Verdict: pass.
4. The proof follows the node's three steps: transport the F operation formulas through GF = id, calculate the inverse product and terminal comparisons sectionwise, then evaluate the RF transport equations. No unused imports or proof dependencies were identified. Verdict: pass.
5. The unit route is preserved: the proof establishes only the four operation equations and leaves construction, invertibility, and naturality to the importing comparison theorem. The repository DAG node and unit realization require no edits. Verdict: pass.

Changed only this report section; no code or DAG changes were needed.
