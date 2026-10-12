## What changed
Added two strictly simpler intermediate theorem modules and proved the target theorem by combining them. The target imports the two helpers and its proof is complete.

## Proved and sorry left
The target `closed_fibre_vanishing_is_divisible` is proved. The two helper declarations `closed_fibre_is_integral` and `closed_fibre_section_is_divisible` remain as named sorry-backed decomposition nodes.

## No longer needed
The target's proof no longer directly imports `Sheaf.AlgebraicGeometry.ValuationClosedFibreSectionVanishing`
or `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`; both remain proof-only imports of the
section-divisibility helper. The corresponding old proof-dependency nodes are no longer direct
dependencies of the target node.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan omitted the explicit intermediate lemmas identifying the quotient fibre with the closed fibre and expressing divisibility from the closed-fibre restriction. These are now split as separate nodes.

## New nodes
`new-valuation-closed-fibre-integral` and `new-valuation-closed-fibre-section-divisible`.

## Second reading by T2
1. Compared the delivered target module with the repository version. The target declaration's
   signature is byte-for-byte unchanged; only its proof and proof-only imports changed. Verdict:
   pass.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no errors, forbidden
   declarations, or sorries in definitions. The two helper theorem sorries are named and documented
   split-off nodes. Verdict: pass.
3. Checked both split-off statements against the source route and small edge cases (including the
   field case allowed by zero in the maximal ideal). Each is a strict intermediate result and neither
   duplicates the target. Verdict: pass.
4. The proof first applies the two helper results and keeps the unit route through those helpers;
   unused direct imports were pruned from the target and helper public interfaces. Verdict: pass.
5. Updated the target node's proof and proof dependencies to match the Lean proof, and verified the
   two new node records match their declarations. Verdict: pass.

Changed the target proof, pruned proof-only imports, and synchronized the target DAG dependencies.
