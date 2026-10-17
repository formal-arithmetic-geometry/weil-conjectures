## What changed

Repaired `Sheaf.AlgebraicGeometry.FormalCompletionPullbackNormalized` against the current
post-sync library. Restored the proof of
`AlgebraicGeometry.exists_formalCompletionPullback_normalized` and changed its proof-only
`import all` from `Sheaf.AlgebraicGeometry.FormalSystemsPullback` to
`WeilConjectures.AlgebraicGeometry.FormalSystemsPullback`, where the helpers now live.
The three public imports, theorem signature, visibility and existing docstring are unchanged.

After substituting the ideal and module equalities, the witness is the inverse component of
`completionPullbackIso`. Its levelwise component is `powerQuotientIso.inv`; rewriting with
`powerQuotientIso_π` and cancelling hom followed by inv proves the required normalization.
The existing node's proof, proof dependencies and unit route already describe this exact
argument, so no DAG route or statement changes are needed. No definitions or consumers change.
The construction also covers the zero module, zero/unit ideals and empty schemes through
the same quotient equations.

Validation through `lcompile.py`: the repaired item compiled in 2.2 seconds. A separate
axiom probe compiled in 3.5 seconds and printed exactly `propext`, `Classical.choice`, and
`Quot.sound`. A source-identical copy of each direct consumer was compiled against the
repaired module in one sandbox overlay: the item took 3.9 seconds,
`Sheaf.AlgebraicGeometry.FormalFlatQuotientMateData` took 5.0 seconds, and
`Sheaf.AlgebraicGeometry.FormalComparisonFlatTransportSquare` took 4.5 seconds. All passed.
The import-direction check permits the direct upstream import.

## Proved and sorry left

Closed the one baseline hole:
`AlgebraicGeometry.exists_formalCompletionPullback_normalized`
(node `lem-weil-pbc-formal-completion-pullback-normalized`).
There are zero remaining holes in the item, zero added holes, and zero split-off theorems.
This is a complete proof with only the three permitted axioms, rather than a decomposition.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.FormalSystemsPullback` and replaced
it with `import all WeilConjectures.AlgebraicGeometry.FormalSystemsPullback`.
The removed module is a public re-export wrapper after the sync and cannot expose the
private helpers of the upstream module. No mathematical node or module is pruned from the
route: `lem-weil-pbc-formal-systems-pullback` and `def-pc-module-pullback` remain needed.
No other imports are removed; the public imports provide the statement's notions.

## Where the brief, the DAG or earlier work was wrong

Repaired the return concerning the red global build after upstream sync `e47efb5a5`.
The former `import all Sheaf.AlgebraicGeometry.FormalSystemsPullback` referred to the
pre-sync owner of the helper declarations. With the same proof and that old import,
`lcompile.py` now fails with `Unknown identifier completionPullbackIso`,
`Unknown constant AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`,
and `Unknown identifier powerQuotientIso`. Importing the actual upstream owner fixes all
three without copying declarations, changing their visibility, or weakening the theorem.

The retained sandbox initially contained only dispatcher marker files. The item and node
were reconstructed from the current shared sources and the returned proof was compared
with those sources. The repair therefore includes an actual import correction, not just
a rebase or unchanged re-push. Existing node metadata and the blueprint unit route are kept.

## Earlier second reading (a previous round; superseded)

1. **Statement preservation.** Compared the delivered module with the repository version. The
theorem signature and all public declarations are byte-for-byte unchanged; only the proof body and its
plain proof import changed. The node statement and existing proof dependencies remain unchanged.
Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no `sorry`, forbidden
commands, or warnings. The direct theorem's transitive environment reports `sorryAx` from older
unrelated imported modules, while the declaration itself introduces no new sorry theorem. The
stage-3 probe permits this inherited `sorryAx` and reports no forbidden axiom beyond the allowed
set. Verdict: pass.

3. **Split-off statements.** No statements were split off and no new nodes were added. The proof
uses the existing `completionPullbackIso` and `powerQuotientIso_π` helpers, with the equality
substitutions and categorical cancellation written directly in the target theorem. Verdict: pass.

4. **Pruning and imports.** Checked the proof imports: the actual helper declarations are owned by
`WeilConjectures.AlgebraicGeometry.FormalSystemsPullback`, so the former Sheaf wrapper import was
removed and replaced by a plain proof import of that upstream module. No public import is used
only for proof, and no additional node or module is pruned. Verdict: pass.

5. **DAG and unit route.** The node's `proof`, `proof_deps`, `proof_origin`, statement, and unit
route agree with the delivered proof. The normalized projection equation follows the planned
completion pullback comparison and its quotient projection identity. Verdict: pass.

Changed during second reading: corrected the report's axiom validation wording to record the
inherited transitive `sorryAx` accurately; no Lean code or DAG metadata required further repair.

## Second reading by K4

1. **Statement preservation.** Compared the sandbox module and node with the shared repository.
The theorem signature, visibility, docstring, and node statement are unchanged; only the proof
body and proof-only import differ. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no `sorry`, forbidden
commands, or warnings. An axiom probe for the theorem reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. Verdict: pass.

3. **Split-off statements.** No split-off declarations or nodes were added. The proof directly
uses the existing completion pullback isomorphism and quotient projection identity, and the
normalization equation is exactly the target statement. Verdict: pass.

4. **Pruning and imports.** The three public imports are statement imports. The sole proof-only
import points to `WeilConjectures.AlgebraicGeometry.FormalSystemsPullback`, which owns the private
helpers; the Sheaf module is only a re-export and cannot provide them. No further import or DAG
dependency can be removed. Verdict: pass.

5. **DAG and unit route.** The node's proof, dependencies, origin, and unit route match the
substitution, inverse-component, projection-rewrite, and cancellation proof. Verdict: pass.

Changed during this reading: appended this review; no Lean declarations or DAG metadata required
repair.
