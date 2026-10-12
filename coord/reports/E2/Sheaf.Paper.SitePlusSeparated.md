## What changed

Replaced the proof of `plus_separated_and_injective` with a proof using Mathlib's
`GrothendieckTopology.Plus.sep` and the existing plus-construction equality
criterion. The proof derives separatedness on each `ZeroHypercover` by factoring
arrows of `sieve₀` through a covering component, then applies the same criterion
to prove injectivity of `toPlus` on `plusObj P`.

## Proved and sorry left

`plus_separated_and_injective` is fully proved; no `sorry` remains in the item.

## No longer needed

The proof does not use `SiteCoveringsCommonRefinement` or any additional bridge
module beyond `SitePlusConstructionPresheaf`; no DAG nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The planned explicit common-refinement argument was unnecessary because Mathlib's
sieve presentation already proves separatedness and the existing presheaf lemma
supplies the covering-family equality criterion.

## Second reading by E2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte for byte unchanged; only its proof, docstring, and import were changed. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds without errors or `sorry`. The proof introduces no axioms or forbidden declarations. Verdict: pass.

3. The proof uses Mathlib's `Plus.sep`, `Sieve.mem_ofArrows_iff`, and the existing plus-construction equality criterion. No new statement was split off, and the route is mathematically valid for every zero hypercover. Verdict: pass.

4. The former common-refinement route is replaced by the shorter generated-sieve argument. The unused `SiteCoveringsCommonRefinement` import and its proof dependency are pruned; the unit's target statement and realized route remain unchanged. Verdict: pass.

5. Updated the DAG node proof and proof dependencies to match the implemented Mathlib/library route. Verdict: pass.

Changed the stale proof docstring, removed the unused public import, and updated the node metadata and report.
