## What changed

Proved `flat_finitePresentation_dense_irreducible_fibres` with its signature unchanged.
Added the proof-only import `Mathlib.RingTheory.Spectrum.Prime.Chevalley`.
The proof uses openness, the residue-field fibre homeomorphism, and the dense-fibre
preirreducibility criterion from Mathlib, followed by a separate nonemptiness argument.
The module compiles cleanly with lcompile.py.

## Proved and sorry left

Closed the sole hole: `flat_finitePresentation_dense_irreducible_fibres`.
No holes remain in the module; no new holes, declarations, or modules are delivered.

## No longer needed

No original imports removed. The proof needs no project dependency modules for
`lem-weil-pbc-flat-finite-presentation-open`, `lem-weil-pbc-irreducible-on-top`, or
`lem-weil-pbc-fibre-spec-homeomorphism`: Mathlib already supplies their required facts
as `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`,
`IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`, and
`PrimeSpectrum.preimageHomeomorphFiber`. All three nodes are pruned from this node's
proof dependencies, with the mathematical route preserved. They had no recorded Lean modules.

## Where the brief, the DAG or earlier work was wrong

The three planned dependencies had no Lean records, although Mathlib has all three
required ingredients. No statement correction was needed. The unit's realized
statement and steps are untouched. Nonemptiness is proved explicitly; the dense-fibre
Mathlib criterion itself gives only preirreducibility.

## Second reading by H1

1. **Visibility and unchanged statements.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; the only module change is a proof-only import and the proof body. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; compilation is clean. Checked the theorem with `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound` occur. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions. Verdict: pass.
3. **Split statements and nodes.** No statements were split off and no new declarations or node files were added. The existing node was updated so its proof and `proof_deps` match the direct Mathlib route. The theorem is tested at the edge cases covered by `IsIrreducible`'s nonemptiness requirement, and no Mathlib or upstream duplicate was introduced. Verdict: pass.
4. **Pruning and route.** The proof uses Mathlib's openness theorem, fibre homeomorphism, and dense-fibre preirreducibility theorem directly; the three former planned project dependencies had no Lean declarations and are therefore removed from `proof_deps`. The unit's statement and realized route remain intact. Verdict: pass.
5. **DAG agreement.** The node's proof text, empty `proof_deps`, and `proof_origin` now describe exactly the declarations used by the Lean proof. Verdict: pass.

Changed the node metadata accordingly and added the proof-only `Mathlib.RingTheory.Spectrum.Prime.Chevalley` import. No holes were added.
