## What changed

Added `FormalFunctionsFiniteSheafQuotientCore` and imported it from the target module.
The target theorem is now proved by combining two strictly smaller interface theorems:
closedness of the canonical finite map and transport of the quotient isomorphism.

## Proved and sorry left

The target declaration `formalFunctions_finite_sheaf_quotient` is proved. Two new
declarations remain sorry: `formalFunctionsFiniteι_isClosedImmersion` and
`formalFunctionsFinite_sheaf_quotient_iso`, with nodes of the same names under
`dag/nodes/sec-proper-base-change/`.

## No longer needed

No imports were removed. The target's direct quotient and closed-immersion imports
are retained by the core module because they describe the proof route.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omits the substantial categorical transport between the chosen
tensor-pullback adjunctions and `formalFunctionsFiniteFMap`; this was isolated as a
strictly smaller theorem rather than leaving a partial proof.

## Earlier second reading (a previous round; superseded)

Open for the second reader: verify that the two intermediate statements are true,
strictly simpler than the target, and that the unit route through the closed-immersion
quotient theorem is preserved.

## New nodes

`lem-weil-pbc-formal-functions-finite-sheaf-quotient-closed` records closedness of the
finite map. `lem-weil-pbc-formal-functions-finite-sheaf-quotient-iso` records the
quotient transport statement.

## Second reading by F1

1. The target signature matches the repository byte-for-byte; only the proof and a
proof-only core import changed. The core contains exactly the two documented split
statements.
2. Both modules compile with `lcompile.py --all`; the only remaining `sorry`s are
`formalFunctionsFiniteι_isClosedImmersion` and
`formalFunctionsFinite_sheaf_quotient_iso`. No forbidden declarations or hollow
definitions occur, and the target theorem is sorry-free.
3. The split statements are true and strictly simpler than the target (closedness
alone, and quotient transport alone), have complete source-based docstrings, and
have matching DAG nodes. No duplicate declaration was found.
4. The proof uses the two split interfaces directly after unfolding the lets. The
node proof metadata matches this route; no imports were removed because the core
keeps the quotient and closed-immersion facts as proof-only imports.
5. The `sk-thm-p1` unit assignment and the closed-immersion quotient route are
preserved.

I added the target node's proof metadata and expanded the split theorem docstrings.
