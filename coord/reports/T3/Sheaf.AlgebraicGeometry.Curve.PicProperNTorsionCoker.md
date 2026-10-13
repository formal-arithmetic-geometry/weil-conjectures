## What changed

Renamed the proved declaration to `Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient` and retained `Scheme.Hom.pic_proper_ntorsion_coker` as a compatibility alias. Updated the node's Lean declaration and proof origin to match; see change record `coord/changes/pic-proper-ntorsion-coker.md`.

Repaired return H10 by removing the alias's deprecation attribute, preserving its signature and proof so the direct importer `PicProperNTorsion.lean` no longer receives a deprecation warning.

Validated the repaired module and an unchanged temporary copy of the direct importer with `lcompile.py`; both compiled without warnings. The temporary importer was removed from the delivery.

## Proved and sorry left

`Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient` is fully proved, and the compatibility alias is proved by direct application. No `sorry` remains and no holes were added.

## No longer needed

No imports or proof dependencies were removed. The former primary declaration name is retained only as an alias.

## Where the brief, the DAG or earlier work was wrong

The checkout does not contain the upstream `Curve/Jacobian.lean` module cited by review #1428; this delivery provides the canonical declaration locally while preserving source compatibility for the existing caller.

## Earlier second reading (a previous round; superseded)

1. **Visible declarations and statements:** Compared the original theorem signature with the compatibility alias; the alias has the same hypotheses and conclusion. The canonical theorem carries the unchanged proved statement. Verdict: pass.
2. **Proof and axioms:** Compiled the module with `lcompile.py`; it succeeds with no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Verdict: pass.
3. **Statements and nodes:** The canonical declaration is the same cokernel statement, with no weakened hypotheses or conclusion. The existing DAG node was updated only in its Lean declaration and proof origin. Verdict: pass.
4. **Shortest route and pruning:** The proof uses the existing Picard decomposition and divisibility declarations and Mathlib quotient isomorphism APIs. No shorter route or removable import was found. Verdict: pass.
5. **DAG and unit route:** The node proof dependencies and unit route remain unchanged and agree with the module proof. Verdict: pass.

## New nodes

None.

## Second reading by T3

1. **Visible declarations and statements:** Compared the delivered module with the repository
version. The cokernel statement is unchanged in hypotheses and conclusion; the canonical name
and compatibility alias are documented by the existing change record. Verdict: pass.
2. **Proof and axioms:** Compiled the module with `lcompile.py`; it succeeds without warnings.
The declarations contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`.
The axiom probe shows only the permitted kernel axioms plus `sorryAx` inherited from the still-open
Picard decomposition/divisibility dependencies. Verdict: pass.
3. **Statements and nodes:** The canonical declaration has exactly the recorded node statement,
and the alias has the original caller-facing signature. No new split-off statement was added.
Verdict: pass.
4. **Shortest route and pruning:** The proof uses the recorded decomposition and divisibility
dependencies, then Mathlib's quotient first-isomorphism APIs. All imports are used by the statement
or proof; no removable import or shorter available route was found. Verdict: pass.
5. **DAG and unit route:** The node's declaration, proof dependencies, and proof origin agree with
the delivered proof, and the unit route remains the decomposition-plus-divisibility route. Verdict:
pass.

Changed only the report: recorded this second reading and retained the worker's canonical theorem,
compatibility alias, and associated node/change record without further code changes.
