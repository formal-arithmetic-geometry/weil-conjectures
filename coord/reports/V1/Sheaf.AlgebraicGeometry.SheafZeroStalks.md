## What changed

Clarified the compatibility module's documentation: no local declaration callers need
adaptation. The repository baseline already retired the duplicate theorem and removed
its two proof-only imports. This delivery changes no declaration, signature, definition,
visibility, import, or target statement.

## Proved and sorry left

Holes closed: none. Holes added: none. There are zero declarations and zero `sorry`s
in this module in both the current repository baseline and this delivery. This is a
second-reading/documentation delivery, not a new proof or decomposition.

## No longer needed

None newly pruned in this delivery. The baseline already removed the proof-only imports
`Mathlib.Topology.Sheaves.Abelian` and `Mathlib.Algebra.Category.Grp.Zero` and retired
`AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalks`. Its node already has empty
`proof_deps`. The two existing public imports are preserved for compatibility.

## Where the brief, the DAG or earlier work was wrong

The worker's report described the earlier retirement as if it were this delivery's change.
The actual repository diff is documentation only. The sandbox also contained stale
maintainer-owned `reviewed_proof` metadata; restored it from the repository.
The upstream theorem's exact signature and axioms cannot be verified here: its module
is absent from this snapshot, as the existing node explicitly records. No new proof
claim is made about that theorem.

## Second reading by V1

1. Compared the complete Lean file and node against the repository with diff.
   Verdict: the Lean change is a module-documentation sentence only; all existing
   signatures (there are no local declarations), imports and visibility are unchanged.
   The earlier declaration retirement is already in the repository baseline.
2. Compiled the delivered module using lcompile.py: exit code 0, no warnings.
   Inspected the complete file: no theorem, definition, sorry, axiom, unsafe, opaque,
   implemented_by or extern occurs as code. There is no local declaration on which
   to run #print axioms. Verdict: clean compatibility module; no new proof claimed.
3. There are no split-off statements or new nodes. Verdict: small-case testing,
   duplicate searches and docstring proof checks for new statements are inapplicable.
   Whole-source rg confirms no caller of the retired declaration remains in lean/.
4. Read the unit record sk-prop-av-pqf-finite and the node. Verdict: no route or
   realized field changes; no new pruning. Both public imports remain unchanged
   because removing compatibility exports would be an interface change. The baseline
   node already has no local proof dependencies.
5. Compared proof, proof_deps, proof_origin and lean records with the repository.
   Verdict: unchanged; the record explicitly identifies the upstream theorem from
   review #1428 and explicitly says its signature is unverified in this snapshot.
   Restored stale reviewed_proof metadata rather than overwriting a later review.

Second reading changed the documentation sentence to avoid implying existing callers
use an unavailable upstream module, corrected the report's baseline/progress claims,
and restored the repository's maintainer-owned review metadata and landed change-record status. No proof was rewritten.

## New nodes

None. The existing change record coord/changes/remove-sheaf-zero-stalks-duplicate.md
records the earlier retirement; it is not evidence of new proof progress here.
