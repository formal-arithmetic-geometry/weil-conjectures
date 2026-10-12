## What changed

Proved `IsLocalRing.depth_over_quotient_ring` with its original signature unchanged.
Added the fully proved private helper `IsLocalRing.depth_eq_of_surjective`: depth is
unchanged along a surjective algebra map between local rings with compatible module
actions. The helper identifies maximal-ideal products by `Ideal.smul_restrictScalars`,
transfers regular sequences by `AddEquiv.isRegular_congr`, lifts lists by
`Function.Surjective.list_map`, and compares the two branches of `Ideal.depth`.
The public theorem applies it to M and to R/I. No new import is needed.
Updated the existing node's proof, proof dependencies and proof origin to match.

Read Stacks Algebra in the local mirror at Definitions 00LF (line 16594), 00LI
(line 17766) and Lemma 0AUK (line 18048). Ran LeanFinder for quotient depth,
Loogle for `AddEquiv.isRegular_congr`, and source grep for scalar-change lemmas;
the latter two located the exact Mathlib tools used.

## Proved and sorry left

Closed the sole hole: `IsLocalRing.depth_over_quotient_ring`
(node `lem-weil-pbc-depth-over-quotient-ring`). Both conjuncts are proved.
The private helper `IsLocalRing.depth_eq_of_surjective` is fully proved.
No sorry remains in this module. No holes were added or split off.
Local compilation passes without warnings. Second-reader scratch-copy `#print axioms`
checks of both declarations show only `propext`, `Classical.choice`, and `Quot.sound`.
The proof treats M=0 through the infinity branch, and handles empty lists and I=0
without extra assumptions. I=top is excluded by the original I≤maximalIdeal hypothesis.

## No longer needed

Removed proof dependency `lem-weil-pbc-surjective-image-noetherian`: quotient
Noetherianity is unnecessary for the actual depth definition or the direct argument.
This node is a Mathlib leaf, with no Sheaf module to remove. All other original proof
dependencies remain. No imports were removed: the original public imports support
the unchanged statement and its local-instance constructions. No other module is
claimed globally unreachable. The blueprint unit's realized statements and steps
are unchanged; this supporting node is below that level.

## Where the brief, the DAG or earlier work was wrong

The plan claimed quotient Noetherianity was required for depth to be defined;
`Ideal.depth` actually requires only a commutative ring and a finite module.
The original node search recorded only weak-regularity scalar transfer as a
candidate; Mathlib also has `AddEquiv.isRegular_congr`, which transfers full
regularity between different scalar rings with the same additive module.
The repository's literature path is absent locally, so the matching Stacks
source was read from the available local mirror. No statement or definition changed.


## Second reading by R2

1. Compared the complete delivered module against the repository using `diff -u`
   and compared the public theorem signature as bytes: identical. The only Lean
   differences are the new fully proved private helper and the replacement of the
   original `sorry` by its two applications. The original docstring, all public
   imports, both equality conclusions, universes and local-instance expressions
   are unchanged. No definitions or target statements changed. Verdict: pass.
2. Compiled the module through `lcompile.py`: exit 0, 1.8 seconds, no warnings.
   Compiled a scratch copy with `#print axioms` for the public theorem and private
   helper: both use exactly `propext`, `Classical.choice`, `Quot.sound`, without
   `sorryAx`. Read every proof step; there is no `sorry`, axiom, unsafe declaration,
   opaque declaration, foreign implementation or data construction from an
   unproved existence theorem. The torsion hypothesis gives the actual canonical
   quotient action; its scalar tower is checked by Lean. Verdict: pass.
3. No statements were split off and no holes were added. The new private helper
   is proved, not an assumed reformulation. It needs surjectivity, local rings,
   compatible actions and module finiteness, and has all of these hypotheses.
   Checked M=0 (both depth branches are infinity), I=0 (identity scalar change),
   empty sequences, and a field with I=0 (nonzero finite modules have depth zero).
   I=top cannot satisfy I≤maximalIdeal. Read Stacks 00LF, 00LI and 0AUK in
   `/tmp/stacks-project2/algebra.tex`: the nonzero final quotient is part of
   regularity and must be preserved. `AddEquiv.isRegular_congr` preserves it as
   well as injectivity on the successive quotients. Verdict: pass.
4. Repeated search with different expressions (`depth.*(surjective|restrictScalars|quotient)`
   and `isRegular_congr`) through `msearch.py ... grep`, and searched the local
   Mathlib depth directory, upstream regular-sequence module and repository Lean
   sources. No pre-existing depth scalar-change theorem was found. The proof
   already uses the full Mathlib regularity transfer, maximal-ideal image/comap
   lemmas and restriction-of-scalars identity directly. Every public import
   provides notions or constructions used in the unchanged public signature;
   no new proof-only public import was introduced. Compared the original
   `proof_deps`: only `lem-weil-pbc-surjective-image-noetherian` is removed,
   correctly listed above, and it is a Mathlib leaf without a module to prune.
   Read `dag/units/sk-thm-p1.json` including `realized`: neither this supporting
   node nor the removed leaf realizes a unit statement or step. Verdict: pass.
5. Compared both JSON records: only `proof`, `proof_deps`, `proof_origin` differ.
   Step 1 describes the exact quotient structures and finiteness instances;
   step 2 describes the identity additive equivalence, list lifting, maximal
   ideal membership and equal lengths; step 3 describes `smul_restrictScalars`,
   the two branches and both applications. Read the quotient-local-structure
   leaf: its recorded Mathlib declarations are precisely those used here.
   The four retained dependencies equal the union of the steps' `uses`, and
   source and proof origin describe the actual direct argument. No new nodes
   require validation. Verdict: pass.

Changed during second reading: added this independent review and explicit axiom
check results to the report. The Lean proof and node changes needed no repair.
One original hole closed; zero holes added; this is a proof, not a decomposition.
