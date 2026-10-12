## What changed

Proved `ModuleCat.finite_torsion_prime_power_successor` without changing its signature.
Added the proof-only import `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.
Constructed multiplication by r using `ZMod.lift`, and reduction using `ZMod.castHom`.
Proved injectivity by integer divisibility and cancellation, surjectivity by
`ZMod.castHom_surjective`, and exactness using integer representatives. Lifted both
maps explicitly to modules over lifted integers and applied extension closure.
The construction also covers e = 0 (ZMod 1 is the zero left term).

## Proved and sorry left

Closed the sole hole: `ModuleCat.finite_torsion_prime_power_successor`
(node `lem-sbc-finite-torsion-prime-power-successor`). No sorry remains and no holes
were added. The proof uses no unproved project dependencies.

## No longer needed

None. No existing imports, nodes, or modules were removed. The DAG's explicit
cyclic short exact sequence route is retained; no auxiliary statement is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The available compiled Mathlib does not expose
`ZMod.lift_injective`, although the read-only source checkout contains it; the proof
instead uses `injective_iff_map_eq_zero` and integer representatives.

## Second reading by F2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only one proof-only import and the theorem proof were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. An axioms probe reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. Verdict: pass.
3. Checked the proof route and edge case `e = 0`: the construction uses the canonical cyclic sequence, with `ZMod 1` as the zero left term, and the prime assumption supplies cancellation. No split-off statements were added, and searches found no duplicate library theorem. Verdict: pass.
4. The proof follows the explicit short-exact cyclic sequence route in the DAG and uses the shortest available Mathlib constructions; the added `ShortComplex.ModuleCat` import is required for `Function.Exact` and short-complex exactness. No imports or proof dependencies can be pruned. Verdict: pass.
5. The node's proof, proof origin, and empty `proof_deps` agree with the Lean proof, which introduces no project theorem dependencies. The unit route is retained. Verdict: pass.

Changed only the proof and its proof-only import; no statements, definitions, nodes, or unit records required repair.
