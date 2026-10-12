## What changed

Added a proved private categorical helper `single_lift_of_homology_presentation`.
The target theorem now reduces its proof to the geometric presentation theorem
`clopenRankStrata_homology_presentation`, which is stated as a named intermediate
result with a documented `sorry`.

## Proved and sorry left

The categorical lifting argument is proved by naturality of the canonical
single-complex/homology isomorphism. The target
`AlgebraicGeometry.clopenRankStrata_homology_lift` is closed from that helper and
the intermediate presentation theorem. The only `sorry` left is
`AlgebraicGeometry.clopenRankStrata_homology_presentation`, node
`lem-sc-clopen-rank-strata-homology-presentation`.

## No longer needed

None; all imports of the original module remain part of the geometric
presentation route.

## Where the brief, the DAG or earlier work was wrong

The original node treated the idempotent splitting and truncation as one
unpackaged step. This delivery exposes that step as a strictly simpler
presentation theorem so the categorical lifting portion can be checked directly.

## New nodes

`lem-sc-clopen-rank-strata-homology-presentation` records the geometric
idempotent-splitting/truncation statement left for a subsequent worker.

## Second reading by N4

1. Compared the delivered module with the repository version. The existing target signature is byte-for-byte unchanged; only a private helper, the split-off presentation theorem, and the target proof were added. Verdict: pass.
2. Compiled the module and all sandbox modules with `lcompile.py`; there are no errors, forbidden declarations, or unsanctioned sorries. The target depends on `sorryAx` only through the explicitly named presentation theorem. Verdict: pass.
3. Checked the presentation theorem against the target's geometric route and DAG node. It is a strictly simpler intermediate statement, with a source, proof description, and node; it does not restate the target. Verdict: pass.
4. The proof uses the shortest available categorical route after the geometric presentation: define the lift by mapping the given arrow through the single functor and composing with the presentation isomorphism, then use naturality. No imports were removed because the geometric presentation route still requires the existing imports. Verdict: pass.
5. Updated the target node's `proof`, `proof_deps`, and `proof_origin` to match the proof, and retained the unit route through the presentation node. Verdict: pass.

Changed the report and synchronized the target DAG node. No theorem statements or public definitions were changed.
