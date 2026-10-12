## What changed

Split the cocycle-homology theorem into two named intermediate declarations. The main theorem now obtains the two additive equivalences from `zariski_etale_resolution_cocycle_equivalences` and applies `zariski_etale_resolution_cocycle_compatibility`.

## Proved and sorry left

The main declaration `zariski_etale_resolution_cocycle_homology` is proved by composition. The two intermediate declarations remain sorry: `zariski_etale_resolution_cocycle_equivalences` and `zariski_etale_resolution_cocycle_compatibility`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires substantial termwise Ext and homology transport infrastructure absent from the current library; these components are recorded as separate strict intermediate statements.

## New nodes

`lem-weil-pbc-zariski-etale-resolution-cocycle-equivalences` and `lem-weil-pbc-zariski-etale-resolution-cocycle-compatibility`.

## Earlier second reading (a previous round; superseded)

The decomposition is structurally valid: the main theorem combines independently named equivalence and compatibility components, while preserving the original target signature and unit route.

## Second reading by N3

1. I diffed the delivered homology module against the repository version. The theorem
   signature is byte-for-byte unchanged; only two proof-only imports and the proof body were
   added. The two intermediate modules are new files and do not alter an existing declaration.
   Verdict: pass.

2. I compiled all three sandbox modules with `lcompile.py --all`; they compile cleanly. The
   only remaining `sorry`s are the two explicitly named split declarations
   `zariski_etale_resolution_cocycle_equivalences` and
   `zariski_etale_resolution_cocycle_compatibility`; there are no sorries in definitions,
   axioms, unsafe declarations, or other forbidden constructs. Verdict: pass.

3. I checked the two split statements and their DAG nodes. The equivalences declaration
   isolates exactly the existence of the two displayed additive equivalences, while the
   compatibility declaration takes arbitrary such equivalences and states precisely the
   cocycle-to-homology equality needed by the target. They are strictly smaller than the
   target and neither duplicates it. Their docstrings identify the Stacks source and the
   corresponding node records carry matching statements and declarations. Verdict: pass.

4. The target proof uses the shortest available route in this library: obtain the two
   equivalences from `zariski_etale_resolution_cocycle_equivalences`, then apply
   `zariski_etale_resolution_cocycle_compatibility`. Both proof-only imports are used; all
   statement imports remain necessary. No old proof dependency can be removed. The unit route
   remains represented by the target and its two strict intermediate nodes. Verdict: pass.

5. I checked that the DAG `lean` records, declarations, proof descriptions, and proof
   dependencies agree with the Lean files. The two new nodes are marked split, cite the target
   as their blueprint ancestor, and use the source and search records supplied by the worker.
   Verdict: pass.

Changed: added this second-reading audit only; no Lean or DAG repairs were necessary.
