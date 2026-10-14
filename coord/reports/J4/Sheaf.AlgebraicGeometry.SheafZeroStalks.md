## What changed

The compatibility module retains its public imports and contains no
local theorem: the duplicate `isZero_of_isZero_stalks` declaration was retired in favor of the
canonical upstream `AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalk`.
A source comment clarifies that these compatibility imports do not re-export that theorem.

## Proved and sorry left

There were no declarations or `sorry`s in the delivered module, so no proof holes were present.
Holes closed: none. Holes added: none. Split-off statements: none.
The canonical theorem is recorded by the DAG as an existing upstream declaration, but its
module is absent from the installed sources. Its signature and axioms were not verified;
this delivery claims no proof of that theorem.

## No longer needed

The local proof plan and its former local declaration are no longer needed. No additional imports
or dependency modules are needed beyond the compatibility module's existing public imports.

## Where the brief, the DAG or earlier work was wrong

This assigned repair already appears in the repository: the duplicate was retired by T3.
The DAG records the canonical upstream name from review #1428, with an explicit note that its
source and exact signature have not been verified. That limitation remains unresolved; the
empty compatibility module does not itself prove the node's mathematical statement.

## New nodes

None.

## Second reading by J4

1. Compared the delivered Lean module and node against the repository with `diff`.
   The module has no existing declaration signatures or definitions. The only source
   difference was an omitted module-comment sentence; restored it. Added a standalone
   comment clarifying the absent canonical re-export. The node is unchanged. Verdict: no interface,
   target statement, or definition change.
2. Compiled the compatibility module using `lcompile.py`: exit code 0, no warnings.
   Inspected the entire file: no declarations, `sorry`, forbidden axiom constructs, or
   hollow definitions. There is no local declaration on which to run `#print axioms`.
   The canonical theorem named by the node is not available in the installed source checkout,
   so its axioms cannot be certified here. Verdict: the delivered module passes;
   no mathematical proof or closure progress is claimed.
3. There are no split-off statements, new modules, or new nodes to check for truth,
   edge cases, duplication, or docstring completeness. Verdict: not applicable.
4. Read the full module, its two public-import sources, the direct importer's proof,
   the duplicate-removal change record, upstream review #1428, and the unit record
   `dag/units/sk-prop-av-pqf-finite.json`. Searched the project and installed upstream
   source roots for both theorem names; found no declaration or caller of the retired
   name. The public imports preserve the already-landed compatibility interface and
   are not newly introduced proof-only imports. The unit's `realized` fields do not
   name this node; no unit step or route was replaced. Old `proof_deps` is empty,
   and no dependency or module is newly pruned. Verdict: no further proof to shorten
   or pruning to perform in this delivery.
5. Compared the entire node JSON: unchanged, including `proof`, `proof_deps`, and
   `proof_origin`. These document the prior retirement, not a new local proof.
   Its `lean.note` explicitly discloses the unavailable upstream source and its
   `lean.statement` remains null. Verdict: consistent as a record of the prior repair,
   with the canonical theorem verification limitation stated above.

Second reading changed only the report's accounting and verification claims, and restored
the repository's explanatory comment in the sandbox module, with a standalone clarification
of the canonical theorem's availability. No proof was changed.

The first dry run refused a report-only delivery because the item's module was unchanged.
The standalone source clarification makes this already-listed repair reviewable without
altering imports, statements, or definitions.
