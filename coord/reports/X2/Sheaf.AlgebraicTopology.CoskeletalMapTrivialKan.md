## What changed

Proved `SSet.rlp_boundaries_of_coskeletal_map` without changing its signature or imports.
Private proved helpers supply injectivity on maps from standard simplices, lifting in degrees
at most n, the truncation bijection for maps into a coskeletal object, and lifting above n.
The proof follows the original six-step Stacks Project Tag 01A6 argument.

For degrees at most n, Yoneda supplies a simplex lifting the target simplex; boundary
extensionality and injectivity below n verify the prescribed boundary. Degree zero uses
Mathlib's empty-boundary extensionality. Above n, the truncated boundary inclusion is an
isomorphism, so the adjunction and invertible units make restriction to the boundary bijective.
The unique extension in V has the required image in U by injectivity of restriction into U.
Finally, unpacking the generating boundary family gives the asserted right lifting property.

## Proved and sorry left

Closed the only original hole, `SSet.rlp_boundaries_of_coskeletal_map`.
No holes added; no `sorry` remains in the delivered module. All four private helpers are proved.
The module compiles cleanly with the required single-file compiler.

## No longer needed

The DAG proof dependency `lem-weil-pbc-simplex-face-factorization` is no longer needed as a
separate dependency: Mathlib's boundary hom-extensionality API supplies that step directly.
No import is pruned; the proof uses the original Mathlib import only. No temporary split-off
module or node is delivered.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was needed. The original six-step route works with
Mathlib's existing boundary, Yoneda, natural-isomorphism and adjunction APIs.

## Second reading by X2

1. **Signature and accidental changes:** Compared the delivered module with the repository version.
   The theorem signature and import are byte-for-byte unchanged; only the proof and private helpers were added.
   Verdict: pass.
2. **Proof and axioms:** Compiled the module with `lcompile.py`; it has no `sorry`, forbidden declarations,
   or warnings. An axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for
   `SSet.rlp_boundaries_of_coskeletal_map`. Verdict: pass.
3. **Split-off statements:** No split-off theorem or node was added. The private helpers are fully proved,
   and searches found no pre-existing declaration that was improperly duplicated. Verdict: pass.
4. **Route and pruning:** The proof follows the recorded six-step Stacks 01A6 route: low-degree boundary
   lifting, the coskeleton truncation bijection, and high-degree lifting. No import or proof dependency is
   unused, and the unit route is unchanged. Verdict: pass.
5. **DAG agreement:** The target node's proof, dependencies, and origin remain consistent with the Lean proof;
   no node fields or statements require changes. Verdict: pass.

Changed only the proof of `SSet.rlp_boundaries_of_coskeletal_map` and added the second-reader audit above.
