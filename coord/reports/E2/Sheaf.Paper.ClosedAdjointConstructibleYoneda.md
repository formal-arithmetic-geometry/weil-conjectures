## What changed

Repaired the returned delivery at 1362f3092 against the current library. The retained
module was already byte-identical to the library, as the landing tool reported.
This packet makes a substantive private proof dependency change in
`Sheaf.Paper.ClosedAdjointConstructibleYoneda`: replace the direct import of
`IntegralConstantModelHeartClosure` by `CondensedCoefficientIsoConstructible`.

The private theorem `bounded_comap_iff` now proves preservation and reflection of
constant-model constructibility from general coefficient restriction. The reverse
implication uses restriction along the inverse map and cancels the two restrictions;
the exact derived homology comparison supplies the bounded version. The rest of the
coefficient-conjugation and two-adjunction Yoneda proof is retained in full.

Every public signature, public import and definition stays identical to the current
library. The node records the implemented proof dependencies and its Lean attachment
matches the current theorem, including its existing exactness instance and coefficient
convention. The previous restoration change record is superseded by
`coord/changes/E2-closed-adjoint-yoneda-coefficient-proof.md`, which lists the current
consumers. No source-library module or target changes.

The revised item compiled through `lcompile.py` in 46.0 seconds, with no errors or
warnings. The delivery command performs the required final compile and preflight.

## Proved and sorry left

The public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.closedAdjointConstructibleYoneda`
(node `det-prop-closed-adjoint-constructible-yoneda`) is completely proved in the
item, as are both private helpers `bounded_comap_iff` and
`support_preserved_of_coefficientIso`.

Current-library direct holes before this repair: zero. Holes closed in this repair:
zero. Direct holes remaining: zero. Holes added: zero. Split off: zero. The one
historical hole of the retained restoration is already closed in the library and
is not counted again. Imported theorems may still have inherited holes; this report
does not assert a sorry-free transitive axiom closure.

## No longer needed

Removed the direct proof import `Sheaf.Paper.IntegralConstantModelHeartClosure`.
Neither its integral weak-Serre theorem nor its private coefficient API is needed
by this argument. General coefficient transport supplies the needed finite-model
facts, and the reflection argument is proved in the existing private helper.
This is removal of a direct dependency only: the module remains transitively
imported through other dependencies. No module is withdrawn or globally pruned.

Relative to the stale node plan, direct proof dependencies
`sk-lem-coefficient-heart` and `det-prop-closed-adjoint-constructible-support` are
replaced by `det-def-localizing-closure-ctf-equals-bc` and
`lem-sfb-rational-closed-support-constructible`, exactly as the already present Lean
proof does. The corresponding direct imports `Sheaf.Paper.CoefficientHeart` and
`Sheaf.Paper.ClosedSupportConstructible` were absent before this repair; no new
removal is counted. Remove the obsolete `sk-lem-coefficient-heart` tool-use entry
and retain `sk-def-localizing-closure`. The unit's support-membership and
counit-compatible Yoneda route stays intact.

## Where the brief, the DAG or earlier work was wrong

The return correctly reported that the old packet's Lean module was already in the
library. Re-pushing it unchanged would not be a repair. This delivery instead
replaces the unnecessary direct integral-heart dependency with general coefficient
transport and proves the required reflection step explicitly.

The retained report described restoration from quarantine and one newly closed hole.
Those descriptions are historical, not changes against the current base. Its old
change record also compared archived signatures rather than the current library;
this packet replaces that record. The current source has the existing exactness
instance and finite-subextension algebraic-closure coefficient, and neither is
changed here. No further statement correction is claimed.

The current node still described the old coefficient-heart/support dependency route;
its proof, proof dependencies and Lean attachment are updated to the actual complete
implementation. The added general coefficient-transport dependency has an existing
node and existing proved transport lemmas, so no new node is needed. Searches and
source reading confirm Mathlib's generic adjoint uniqueness and Yoneda lemmas provide
the formal comparison but not the geometric support-membership assertion.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
