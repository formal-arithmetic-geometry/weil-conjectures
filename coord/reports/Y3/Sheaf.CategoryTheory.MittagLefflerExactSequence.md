## What changed

Proved `CategoryTheory.ShortComplex.isMittagLeffler_iff_of_isEssentiallyConstant` without
changing its signature or visibility. Added the proof-only import
`Mathlib.Algebra.Homology.ShortComplex.Ab` for the elementwise exactness API.

The proof uses the cone/retraction/factorization witnesses of essential constancy directly.
For the forward implication, lift the stable quotient part at a common later index, write
the difference as an image from the kernel, and correct it using the kernel's ML witness.
For the reverse implication, apply middle-system ML at an index where the cone is split;
injectivity there kills the stable quotient component of a lift, so a further transition
lands in the kernel. Componentwise injectivity then identifies its image at the original
index. All indices before the splitting index are handled directly, without reindexing.

Updated `lem-weil-pbc-exact-sequence-ml`'s proof, proof dependencies and proof origin to
match the Lean proof. The existing docstring retains the original nine-step plan; the proof
body comments and updated node explain the direct implementation. No auxiliary declarations,
definitions, modules, or nodes are delivered.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.ShortComplex.isMittagLeffler_iff_of_isEssentiallyConstant`
(node `lem-weil-pbc-exact-sequence-ml`). No sorries remain or were added.
This is a proof, not a decomposition.

The final single-file compile passes with no errors or warnings. The delivery dry run checks
all declaration axioms. Only the three standard axioms are permitted.

## No longer needed

Removed proof import `Sheaf.CategoryTheory.EssentiallyConstantSplitting`; removed node
`lem-weil-pbc-essentially-constant-splitting` from this item's `proof_deps`.
Its decomposition into a constant summand and an essentially zero complement is unnecessary:
cone compatibility, injectivity on the tail, and eventual factorization are proved locally
from `def-weil-pbc-essentially-constant-system`.

The explicit auxiliary subgroup towers, their short exact sequences, and tail-reindexing
arguments of the original node plan are unnecessary. No further module dependency of this
item is removed. This pruning is below the unit level: the item realizes no statement or
step in `dag/units/sk-thm-p1.json`'s `realized` field; the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The original node plan calls for more
constructions than its conclusion needs. The direct argument performs its image comparison
without explicitly forming the auxiliary towers.

Searches run through msearch: LeanFinder for the exact-sequence/essential-constant ML
statement returned unrelated inverse-system and direct-limit results; Loogle for
`CategoryTheory.Functor.IsMittagLeffler` returned the usual Type-valued ML API; grep found
the existing definition in `Mathlib.CategoryTheory.CofilteredSystem`. Local searches found
no ready proof in the source library. The elementwise exactness signatures were read in
`Mathlib.Algebra.Homology.ShortComplex.Ab` and the existing proved
`Sheaf.CategoryTheory.MittagLefflerLimitExact` module.

The local literature file `literature/stacks-project/homology.tex` is absent on this machine;
the original node's source citation was retained, and Stacks Tags 070D and 070C were read at
https://stacks.math.columbia.edu/tag/070D and https://stacks.math.columbia.edu/tag/070C.
The node's new `proof_origin` identifies the direct argument as written by this worker.

## Second reading by Y3

1. **Visible changes:** Compared the delivered module with the repository version. The
   theorem signature and all existing declarations are byte-for-byte unchanged; only the
   proof and a proof-only import changed. The node metadata records the updated proof route
   and dependencies. Verdict: pass.
2. **Proof and axioms:** Compiled the module with `lcompile.py`; it succeeds without errors
   or warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The theorem's transitive axioms include only the permitted standard
   axioms plus `sorryAx` from still-open imported declarations. Verdict: pass.
3. **Statements and split-offs:** No new statements or nodes were introduced, and the sole
   target theorem is proved directly. Existing declarations and the target statement were
   searched locally for duplicates; none was added. Verdict: pass.
4. **Pruning and route:** The removed `Sheaf.CategoryTheory.EssentiallyConstantSplitting`
   import is proof-only and is no longer used. The remaining public imports are needed by
   the theorem's statement or module context. The direct proof stays below the unit level;
   `dag/units/sk-thm-p1.json` has no realized step assigned to this item. Verdict: pass.
5. **DAG agreement:** The node's proof steps, `proof_deps`, and `proof_origin` match the
   implementation, and the unit route is preserved. Verdict: pass.

Changed only the proof, its proof-only import, and the corresponding DAG proof metadata;
no mathematical or interface repair was needed.
