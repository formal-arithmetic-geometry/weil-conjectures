## What changed

Proved `AlgebraicGeometry.Scheme.cechDifferential_repeated` by extracting a repeated pair from non-injectivity, rewriting the differential with the decomposition interface, and applying the cancellation interface. Added the two named stage-3 interfaces as separate modules.

## Proved and sorry left

Closed the target theorem `cechDifferential_repeated`. The two strictly smaller interface theorems remain as named `sorry`s: `cechDifferential_repeated_decomposition` and `cechDifferential_repeated_cancellation`.

## No longer needed

None; the original imports are retained, and the proof uses only the two new interface imports and `Function.not_injective_iff`.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omitted the substantial finite-sum decomposition and signed cancellation details. These are recorded as separate interfaces for parallel proof.

## New nodes

`lem-pc-cech-differential-repeated-decomposition`, `lem-pc-cech-differential-repeated-cancellation`.

## Second reading by T3

1. Compared the delivered target module with the repository version. The existing theorem
   signature is unchanged; the only target change is its proof and its proof-only imports.
   The two added interface modules have new declarations recorded by matching DAG nodes.
   Verdict: no accidental statement or definition change.
2. Compiled all three delivered modules with `lcompile.py --all`. They compile without errors;
   the only remaining `sorry`s are the two named interface theorems listed above. No axioms,
   unsafe declarations, or hollow definitions were added. Verdict: pass.
3. Checked the two split statements against the finite-sum expansion and signed cancellation
   argument. Each is strictly smaller than `cechDifferential_repeated`, has a source and
   complete proof sketch in its docstring, and has a corresponding DAG node. Verdict: pass.
4. Checked the proof route and pruning. The target extracts a repeated pair, applies the
   decomposition interface, and then the cancellation interface; all original public imports
   remain required by the signatures. No old proof dependency is silently bypassed. Verdict:
   pass.
5. Checked the DAG `proof`, `proof_deps`, and `proof_origin` against the Lean proof and verified
   that the unit route remains represented by the target and its two strictly lower interfaces.
   Verdict: pass.

Changed after this reading: added this review record only; no Lean declarations or DAG
statements were changed.
