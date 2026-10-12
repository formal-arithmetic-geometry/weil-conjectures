## What changed

Proved `Module.free_prime_mem_localized_iff` in
`lean/Sheaf/RingTheory/FreePrimeMembership.lean`, with the existing signature and
public imports unchanged. Kept the first worker's correct scalar criterion proof.
The vector argument now uses Mathlib's localization of ideal scalar products,
equality of fractions to clear denominators, and the finite coordinate expansion.
Added only the proof import `Mathlib.RingTheory.LocalProperties.Basic`, which supplies
`Ideal.localized'_eq_map` and publicly imports the other required Mathlib lemmas.
Updated the existing node's proof description to match this denominator argument.
Restored the original declaration documentation and aligned its proof description.

## Proved and sorry left

Closed the original hole `Module.free_prime_mem_localized_iff`
(node `lem-sc-free-prime-membership`): both the vector and coordinate conjuncts
are proved. Original holes closed: 1 of 1. Holes added: 0. Sorries left: none.
This is a complete proof, not a decomposition. The provisional split theorem
`Module.free_prime_mem_localized_vector` and node
`new-free-prime-vector-criterion` have been removed rather than delivered.
The scratch `#print axioms Module.free_prime_mem_localized_iff` prints exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

## No longer needed

No old proof-dependency node or original import is removed: both
`def-weil-pbc-module-localization` and `def-weil-pbc-localization-at-prime` are used.
No baseline module is pruned. Removed the sandbox-only vector split theorem and
its node. Replaced the first worker's two proof imports
`Mathlib.Algebra.Module.LocalizedModule.Submodule` and
`Mathlib.RingTheory.Localization.Ideal` with the single necessary proof import
`Mathlib.RingTheory.LocalProperties.Basic`, which provides them transitively.
A trial compile showed a separate `Mathlib.Algebra.BigOperators.Pi` import redundant;
it is omitted.

## Where the brief, the DAG or earlier work was wrong

The first worker left almost all the original difficulty in a vector split theorem.
It is true but unnecessary: general Mathlib submodule localization lemmas close it.
Its node also pointed to a theorem in the item's own module instead of a new module.
No new statement or node is needed in the final delivery. The original DAG's
coordinate argument can be implemented more directly by clearing a common denominator;
the two original proof dependencies and the unit-level route are preserved.

## Second reading by G2

1. Compared the delivered file against the repository version using `diff` and
   checked the existing theorem signature by exact string comparison: byte-for-byte
   unchanged. Verdict: pass. The two public imports and module visibility are unchanged;
   there is no definition or interface change and no change record is required.
2. Compiled the whole delivered module locally through `lcompile.py`, without errors
   or warnings. Compiled a scratch copy with `#print axioms`: only `propext`,
   `Classical.choice`, and `Quot.sound`. Checked that no `sorry`, `axiom`, `unsafe`,
   `opaque`, `implemented_by`, or `extern` appears in the delivered Lean. Verdict: pass.
3. Read and checked the provisional vector statement: it is true for n=0 (zero module,
   empty coordinate condition), n=1 (scalar membership), and the zero vector.
   The zero ring has no prime ideal, so yields no exceptional case. Searched with
   leanfinder for localization of ideal scalar products, loogle for
   `Submodule.localized'_smul`, and grep for coordinate expansions and localized products;
   also searched both roots of the project. Mathlib provides the needed strictly smaller
   ingredients. Removed the provisional theorem and node and proved the vector clause
   inline. Verdict: no split-off statements remain.
4. Read from the original theorem downward. Used Mathlib's
   `Submodule.localized'_smul`, `Ideal.localized'_eq_map`, `Submodule.localized'_top`,
   `Submodule.mem_localized'`, `IsLocalizedModule.mk'_eq_mk'_iff`, and
   `pi_eq_sum_univ'`; retained the correct scalar argument. Checked imports and removed
   redundant proof imports. `## No longer needed` accounts for every old dependency:
   neither is pruned. Read `dag/units/sk-thm-curveestimate.json`: the item's node is
   below the unit's realization, and neither its statement realization nor its steps
   are bypassed. Verdict: pass.
5. Read the existing and provisional nodes against the Lean. Updated only the existing
   node's proof text; its proof dependency union remains the two localization definitions,
   and its literature proof origin still applies. Removed the provisional new node.
   Verdict: the final node agrees with the Lean, with no new nodes to validate.

Second reading changed: completed the vector proof without adding any lower holes,
removed the vector split theorem and node, restored and aligned the theorem documentation,
minimized the proof imports, aligned the existing node's proof, and corrected this report.
