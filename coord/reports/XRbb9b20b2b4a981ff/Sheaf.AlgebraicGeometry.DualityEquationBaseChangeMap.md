## What changed

Change record: `coord/changes/dualityEquationBaseChangeMap-repair.md`.

Removed the redundant final `show _ from` in
`AlgebraicGeometry.dualityEquationBaseChangeMap`. It introduced a local alias after
elaboration that survived the consumer's eleven-name `extract_lets` step, hiding
the mate expression from its rewrite. The definition again ends directly in
`(mateEquiv adjf adjf' (inv β)).app K`.

All signatures, docstrings, imports, visibility and mathematical data are preserved.
`ProperFlatOpenSquareMateIso.lean` is copied unchanged from the broken-tip snapshot.
The DAG node's inverse-mate construction and proof dependencies remain unchanged.

Validation used only separate single-file invocations of
`python3 /home/ubuntu/weil-launcher/lcompile.py <file>`, in dependency order:
`DualityEquationBaseChangeMap.lean` and `ProperFlatOpenSquareMateIso.lean`.
Both completed with exit code 0 and no warnings or errors, within 60 seconds each.
These checks use the compiler wrapper's published compiled imports; they do not
constitute a fresh global build. The independent reader handles delivery and the
fresh dependency check. No server compile, multi-module build, delivery, push,
`.check` file or second-reading evidence was created.

## Proved and sorry left

Holes closed: none. Holes added: none. Split-off declarations: none.
Neither `dualityEquationBaseChangeMap` nor
`proper_flat_openSquare_mate_isIso` contains a `sorry`.
No axiom rules changed; existing upstream open results remain upstream obligations.

## No longer needed

None. No imports, nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery described `show _ from` as elaborationally redundant and
checked only the producer. Although the resulting morphisms are definitionally
equal, this wrapper changes the let structure exposed by downstream proof tactics.
The failure report identifies `ProperFlatOpenSquareMateIso.lean:190`:
`rewrite` could not find `((mateEquiv adjf adjf') (inv β)).app K` in
`IsIso this✝¹`. Removing the wrapper restores the shape expected by that proof.

## Forced adaptations

None. The consumer is byte-for-byte unchanged from the supplied snapshot.
The repair changes only the producer's final expression, by deleting `show _ from`.

## Second reading by XRbb9b20b2b4a981ff

Independent review on 2026-10-14, with request.json, delivery.diff, both complete
Lean modules, the node, change record, report, and the stage-3 review instructions
open. Verdict: PASS for the bounded red-build repair.

1. Interface and mathematics: compared both modules with the supplied repository
   and the producer with the failed delivery recorded in the packet. All existing
   signatures, docstrings, visibility and imports are byte-for-byte unchanged.
   The current repository already has the direct final mate expression; relative
   to that repository the producer adds only two explanatory comments. Relative
   to the recorded failed delivery the repair removes only `show _ from`.
   The consumer is byte-for-byte identical to the repository. In a scratch copy,
   duplicated the old definition from the change record under a fresh name and
   proved equality of the entire old and repaired functions by `rfl`. This
   compiled in 7.4 seconds. Thus all downstream statements, including targets,
   retain their meaning. The change record's Old/New blocks are verbatim and
   differ only by this wrapper; its user table covers every source use found.

2. Compilation and trust: independently compiled the two delivered files in
   dependency order using only lcompile.py, which freshly emitted the producer
   into the sandbox overlay before compiling its consumer. Both passed without
   warnings or errors: 7.2 seconds and 20.5 seconds respectively, each below
   60 seconds. A separate scratch reconstruction of the failed producer compiled
   in 7.3 seconds, and its unchanged consumer failed in 15.1 seconds at line 190
   with the exact recorded rewrite failure, `IsIso this✝¹`, and the same
   transparency/type-correctness diagnostic. This establishes that the repair
   addresses the sole compiler failure listed in request.json, including its
   accompanying diagnostic, rather than compiling against a stale producer.
   Scratch copies with `#print axioms` and the delivery's axiom probe compiled
   in 7.3 and 20.6 seconds. Both public declarations use only `propext`,
   `Classical.choice`, `Quot.sound`, and pre-existing upstream `sorryAx`;
   the reconstructed old definition has the same axiom list. No direct
   `SHEAF-SORRY` or forbidden-axiom result appeared. Neither delivered source
   contains `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`,
   or an explicit `sorryAx`. The probe's own long-line warning is confined
   to appended scratch instrumentation. No axiom or hole workaround was added.

3. Split statements: none added or removed. There is no restatement, weakened
   theorem, hollow definition, or arbitrary new choice of mathematical data.
   The inverse remains the inverse of the fixed invertible base-change
   transformation. No new lemma requires a node, edge-case test, or search.

4. Route and pruning: read the naturality construction and the unchanged
   consumer proof, including the existing generic `secondMate_formula` in
   QCohInverseBaseChangeMate. Its iterated-mate/conjugate identity identifies
   exactly this inverse mate with the node's unit/inverse-conjugate/counit
   expression. The repair changes no proof route and needs no new import.
   The public imports supply the categories, functors and signature data;
   the private Mates import supplies the definition's construction. The
   consumer already uses the existing generic identity and geometric
   restriction theorem. No imported module or old proof dependency became
   unnecessary. Checked sk-thm-picard-duality's realized record: unchanged,
   with no bypass of a unit step. Holes closed: zero; holes added: zero;
   pruned modules: none. This is a build repair, not new proof progress.

5. DAG and record: the definition's restricted functors, lifted natural
   transformation, reflected isomorphism and inverse mate agree with the
   node's proof and proof_origin. Its proof_deps equal the union of the
   listed step uses and remain unchanged. The only node difference against
   the current repository is historical reviewed_proof metadata, which is
   outside this delivery's editable node fields; no mathematical node field
   differs. No new nodes or statement changes are proposed.

Second-reader changes: appended this actual independent review, added the explicit
change-record path required by preflight, and wrote .check.
No Lean, DAG, or change-record correction was needed. All compile experiments
were local, through lcompile.py, with remote fallback disabled; no lake build
or server compilation was used.
