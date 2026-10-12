## What changed

Repaired the target by removing its duplicate top-level `product_zero_iff` declaration.
The same proof is now a local helper inside
`closedImmersion_coherentFormal_equivalence_termwise`, so the target uses no second
library declaration with a statement already present in
`ClosedImmersionCoherentEquivalence`. The target theorem and its previously delivered
proof remain otherwise unchanged.

## Proved and sorry left

`AlgebraicGeometry.closedImmersion_coherentFormal_equivalence_termwise` remains proved
with no direct `sorry`. No new declarations or holes were added.

## No longer needed

The former private top-level `product_zero_iff` declaration in the target is no longer
needed. No imports or DAG proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was rejected because its private helper had exactly the same
statement as `AlgebraicGeometry.product_zero_iff` already declared in
`ClosedImmersionCoherentEquivalence`. That module imports this target, so importing it
here would create a cycle. Making the helper local removes the duplicate declaration
while preserving the proof and the existing interfaces.

## Second reading by W3

1. Compared the delivered module with the repository version: the target theorem
   signature is unchanged; only proof imports and proof text differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py`; there are no errors, forbidden
   declarations, or `sorry` in definitions. Verdict: pass.
3. Checked the split component statement and node against the source and searched for
   duplicates. It is strictly simpler, true, needed, and has no hollow definition.
   Verdict: pass.
4. The proof follows the unit route through pushforward conditions, annihilation,
   full-faithfulness, and formal-systems pullback; the local helper avoids an import
   cycle. Verdict: pass.
5. Target and component DAG records agree with the Lean proof and unit realization.
   Verdict: pass.

Changed the target by keeping `product_zero_iff` local. No new holes were introduced.

## New nodes

No new nodes were added by this repair. The delivered existing component node
`lem-weil-pbc-closed-immersion-formal-pushforward-conditions` remains part of the
previous delivery and is unchanged.
