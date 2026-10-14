## What changed

Proved `exteriorPower.isLocalizedModule_of_wedge` in
`lean/Sheaf/LinearAlgebra/ExteriorPowerLocalization.lean`, with its statement and visibility
unchanged. Three proved private helpers extend multilinear maps by currying, establish
uniqueness by clearing a common denominator, and preserve alternation while upgrading
coordinate maps to B-linear maps. The main proof constructs the two comparison maps and
proves both inverse identities before transporting the localization structure.

Added proof-only imports `Mathlib.RingTheory.Localization.Module` and
`Mathlib.Algebra.Module.LocalizedModule.Int`. Updated the existing node's proof and
proof_origin to describe the actual argument. No other module or interface changed.

## Proved and sorry left

Closed the only original hole: `exteriorPower.isLocalizedModule_of_wedge`
(node `new-v2-exterior-power-localization`). No holes added and no sorry remains.
The private helpers `exteriorPower.extend_multilinear`,
`exteriorPower.localized_multilinear_ext`, and `exteriorPower.extend_alternating`
are fully proved. This is a proof, not a decomposition into remaining statements.

The proof works uniformly in degree zero, for arbitrary modules, and when zero belongs
to S. The induction starts with the empty multilinear map; denominator cancellation
uses invertibility in a localized module, which also holds for the zero module.

## No longer needed

No original import, node, or module was pruned. Both original definition dependencies
remain used. Removed the trial proof import `Mathlib.LinearAlgebra.Multilinear.Curry`
after compilation showed its API is already available through the retained imports.
No new dependency on a sorry-containing Sheaf or WeilConjectures module is introduced.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or unit route was found. The fraction construction can be
implemented entirely with existing Mathlib APIs: curry the last variable, localize
the linear map, and uncurry. A common denominator then handles both uniqueness and
alternation, avoiding a separate quotient-level fraction construction. The DAG proof
was updated to record these fully proved steps. No new nodes or forced adaptations.

## Second reading by V1

1. Compared the delivered module with the repository version. The theorem signature,
   visibility, and all existing declarations are unchanged; only proof-only imports,
   private helpers, and the target proof were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings.
   There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or
   `debug.skipKernelTC` declarations. The target's axioms are exactly
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the proof route and duplicate statements against the library and the
   Mathlib searches recorded in the node. The private helpers are strictly internal
   reductions, no new public statement was added, and the target statement is
   unchanged. Verdict: pass.
4. Checked pruning and imports. The three public imports remain needed by the target
   interface; the two added imports are plain proof-only imports. The node's proof and
   proof dependencies describe the extension, denominator cancellation, alternation,
   and inverse-map argument. No old dependency or module became unnecessary. Verdict:
   pass.
5. Checked the DAG node and unit route. The node's Lean declaration and statement
   agree with the module, its proof and proof origin match the code, and the argument
   follows the unit's localization-of-exterior-powers step through the universal
   property and localization equivalence. Verdict: pass.

Changed after this reading: added this review record only; no Lean or DAG changes were
needed.
