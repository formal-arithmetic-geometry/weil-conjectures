## What changed

Addressed return H10 by retaining the repository's inline `Classical.choose` mate
body in `schemeDerivedBaseChangeMap`, with default recursion depth. The timed-out
local-witness refactor and `maxRecDepth 100000` option are absent. Relative to the
current repository, the Lean file differs only by the H10 repair comment. Existing
signatures, definition bodies, theorem proof and imports are byte-for-byte unchanged.

## Proved and sorry left

Holes closed: none. Holes added: none. No source-level `sorry` remains in this
module. `AlgebraicGeometry.exists_schemeDerivedAdjunction` already has a proof;
`AlgebraicGeometry.schemeDerivedBaseChangeMap` already has the inline mate body.
This delivery is a returned timeout repair, not mathematical proof progress (0 of
0 existing holes closed; 0 split off). The fixed-counit normalization repair in
`coord/hollow-definitions.md` remains unresolved; restoring the previous definition
and naming witnesses do not solve it.

## No longer needed

No imports, nodes or modules pruned. The excessive recursion-depth option and the
local-witness implementation from the returned delivery are no longer used.
The current repository already contains the restored implementation.

## Where the brief, the DAG or earlier work was wrong

Return H11 and the old report referred to local witness bindings that are absent
from the actual delivered source. No `schemeDerivedBaseChangeAdjunction`
declaration was added. The previous change record described nonexistent changes
and was removed from this delivery. The earlier report's normalization claim was
incorrect: a local `let` does not fix the choice of universal counit.

The existing DAG proof accurately describes the derived adjunction argument and
mate formula. Its unit `sk-thm-picard-semicon` currently has empty `realized`
statement and step arrays; this pre-existing incompleteness is unchanged.

## Second reading by J4

1. Compared the full module against the repository using `diff`: only the H10
   module comment differs. All declaration signatures, visibility, definitions and
   proof bodies are unchanged. No statement or definition change record is needed.
2. The delivered module compiled through `lcompile.py` in 52.4 seconds with no
   errors or warnings. Scanned the complete source: no `sorry`, forbidden
   declaration or hollow definition occurs. The scratch-copy `#print axioms`
   checks compiled in 58.9 seconds: both declarations depend only on `propext`,
   `Classical.choice` and `Quot.sound`, with no `sorryAx`.
3. No split-off statements or new nodes exist, so there are no new edge cases or
   duplicate split lemmas. Read the existing normalization theorem and its proof:
   it derives the underived adjunction, then uses the derived-unit factorization
   and naturality of the right-derived unit to establish the displayed equation.
   It does not establish independence from the choice of left-derived counit.
4. The proof already uses the generic `Adjunction.derived` and
   `derivedη_fac_app` route. Retained the return-mandated inline definition and
   imports. The unit route is unchanged; no pruning is claimed.
5. Compared the delivered node with the repository: identical. Its `proof`,
   `proof_deps` and `proof_origin` match the unchanged argument, through K-flat
   preservation, derived adjunction and the pullback-composition mate.

Changed during this reading: corrected the stale report, removed the inaccurate
change record, and independently checked the restored source. No Lean declaration
was changed during this reading.
