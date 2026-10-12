## What changed

Added `TotalFreeFiltrationCokernelOddAux` and imported it from the target module. The target theorem now unwraps its endpoint `Nonempty` witness and applies the core quotient theorem.

## Proved and sorry left

`CochainComplex.TotalFreeFiltration.cokernel_odd` is proved by reduction to `cokernel_odd_core`. The new declaration `CochainComplex.TotalFreeFiltration.cokernel_odd_core` remains `sorry`; it is the degreewise odd filtration quotient calculation and has node `lem-pc-derived-total-filtration-cokernel-odd-core`.

## No longer needed

None. The stable filtration terms import remains needed by the auxiliary theorem.

## Where the brief, the DAG or earlier work was wrong

The DAG plan omitted an explicit intermediate theorem for the core degreewise quotient calculation, so it is split off here.

## New nodes

`lem-pc-derived-total-filtration-cokernel-odd-core` records the strictly more explicit core calculation used by the target theorem.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged. The new core statement is a direct strengthening of the endpoint input from `Nonempty` to an explicit isomorphism and is used exactly once; its proof remains open for the next worker.

## Second reading by S1

1. Compared the delivered target module with the repository version. The existing
   theorem signature and all definitions are byte-for-byte unchanged; only its proof
   and the proof-only import were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The target theorem has
   no `sorry`; the only remaining `sorry` is the named split theorem
   `CochainComplex.TotalFreeFiltration.cokernel_odd_core`, and no forbidden
   declarations or definitions containing `sorry` were introduced. Verdict: pass.
3. Checked the new core statement against the endpoint quotient argument and its
   small boundary cases (including empty index type and `j = 0`). It is a true,
   strictly simpler strengthening of the target input, with a complete source and
   proof description in its docstring and matching DAG node. No existing library
   declaration duplicates it. Verdict: pass.
4. Read the proof from the target downward. It unwraps the `Nonempty` witness and
   applies the core calculation directly; the public `TotalFreeFiltrationTerms`
   import remains needed by the statements, while the auxiliary module is imported
   privately for the proof. The unit route through the stable filtration terms is
   retained. Verdict: pass; no pruning was available.
5. Compared the DAG node proof, dependencies, origin, and unit with the Lean proof.
   The target node now uses the auxiliary core node, and the auxiliary node records
   the stable-filtration dependency and source. Verdict: pass.

Changed: added the proof-only import and reduction proof in
`TotalFreeFiltrationCokernelOdd.lean`, added the split core theorem module and its
DAG node, and documented this second reading.
