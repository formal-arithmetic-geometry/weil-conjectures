## What changed

Proved `LinearMap.extOne_directSum_bijective` in
`lean/Sheaf/Algebra/ExtOneDirectSum.lean`, with its existing signature and public imports
unchanged. Added the proof-only import `Mathlib.Algebra.Module.Shrink`. All helpers are private and fully proved in the same module.

The proof constructs `(N × ⨁ j, E j) / range(sum, -lmap u)`, proves its short exactness,
and derives its universal property. The maps from the summand extensions to its pullbacks
are bijective by an elementary short five lemma proved in the file. A proved set-theoretic
surjection from `N × P` supplies the Small instance needed to transport the assembled
extension to `Type (max w x y)`.

For injectivity, assemble the pullbacks of the first extension. Its universal property gives
maps to both original extensions, commuting with the endpoints; both are bijective by the
same short five lemma. Their composite gives the required endpoint-fixed equivalence.
The existing node's proof now records this common-presentation argument and universe step.
The unit's route is unchanged.

## Proved and sorry left

Closed 1 original hole: `LinearMap.extOne_directSum_bijective`
(node `lem-weil-pbc-ext-one-direct-sum`). Added 0 holes; split off 0 statements.
No `sorry` remains in the item or any new declaration. No new modules or nodes.
Single-file compilation passed without warnings. The delivery dry run performs the axiom
probe and preflight checks.

## No longer needed

Removed the redundant proof-only import `Mathlib.Logic.Small.Basic` during the second
reading; its declarations are already available through the remaining imports. No
original import or project module was removed; the three existing proof dependency nodes
`def-weil-pbc-direct-sum-modules`, `def-weil-pbc-exact-sequence`, and
`def-weil-pbc-quotient-module` remain relevant Mathlib leaves. No additional Sheaf or
WeilConjectures module is needed. In particular the downstream
`Sheaf.RingTheory.DirectSumExtensionAssembly` is not imported (it depends on this result).
The separate kernel-factorization/gluing argument in the original plan is replaced by the
universal property of the already constructed quotient and the short five lemma; it had
no separate node or import to prune.

## Where the brief, the DAG or earlier work was wrong

No statement error. The original plan omitted the universe reduction required by the Lean
signature: its raw quotient depends on the universe of the representatives `E j`, whereas
the conclusion requires `Type (max w x y)`. The proved `small_middle` helper resolves this
using a set-theoretic section and `Shrink.linearEquiv`.

Searches through the prescribed leanfinder, loogle and grep tools, and local Mathlib and
library searches, found no arbitrary-family Ext theorem to apply directly. The finite
biproduct results do not cover this statement. Mathlib's DFinsupp range/kernel formulas
suffice for the direct-sum exactness step.

The empty-index and zero-module cases require no exception: direct sums, the quotient,
all universal properties and the short five lemma proofs work without nonemptiness or
nontriviality assumptions. All constructed data use actual quotient operations or proved
surjectivity; there is no unproved witness selection or hollow definition.


## Second reading by U3

1. **Visible declarations unchanged: PASS.** Diffed the sole delivered module against
   the repository. The existing public theorem signature is byte-for-byte identical,
   as are its docstring, universes and the two public imports. The only new declarations
   are private proof helpers; no existing definition changes and no change record is
   needed. There are no adapted modules.
2. **Proof and axioms: PASS.** Independently compiled the module without errors or
   warnings. A scratch copy with `#print axioms LinearMap.extOne_directSum_bijective`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Inspected all helpers and scanned for forbidden declarations and kernel bypasses;
   there are no holes or forbidden constructs. The quotient is constructed explicitly;
   the only set-theoretic choices are from proved surjectivity or proved equivalences.
3. **Split statements and edge cases: PASS.** No split-off statement, new public
   statement, new node, or new hole exists. Checked the private reductions: the signs
   in the quotient relation identify summand copies of N with its distinguished copy;
   exactness and the universal property follow directly. The short-five argument uses
   precisely target endpoint injectivity, source endpoint surjectivity, and exactness
   of both rows. Pullback maps and their inverses preserve both endpoints. For empty J
   the quotient is N and P is zero; for singleton J it recovers the given extension;
   zero N or zero C causes no failure. The set-theoretic surjection N × P → F justifies
   shrinking even when the representative universe is larger than both endpoints.
4. **Shortest route and pruning: PASS with one import repair.** Independently searched
   using leanfinder (extension classes of a coproduct), loogle (Exact/Bijective/LinearMap),
   and grep (coproduct Ext and right-exact five lemmas), and searched the local library
   and upstream Lean modules. Found categorical Ext and finite-coproduct results, but
   no direct arbitrary-family theorem matching this unbundled, independent-universe
   statement. Mathlib's four/five lemmas use longer diagrams and do not replace the
   quotient construction; the small elementary endpoint-fixed argument is retained.
   All three old proof dependencies are used, so none is missing from No longer needed.
   Read sk-thm-p1's steps and realized fields: this item is below the unit level, and
   neither the unit route nor any realized node is bypassed. Independently compiled
   without `Mathlib.Logic.Small.Basic`; removed that redundant direct import. The other
   imports supply the public signature, quotient operations, exactness and shrinking.
5. **DAG agrees: PASS.** Compared both node versions: only proof and proof_origin
   differ. The seven steps describe componentwise exactness, explicit quotient assembly,
   pullback identification and shrinking, and the common-presentation comparison used
   in Lean. The union of their uses equals the unchanged proof_deps. The statement,
   Lean record, source, chapter and unit are unchanged; no new-node fields are required.

Changed only the redundant direct proof import and the report, including this second
reading. Retained the correct proof and DAG. Closed 1 original hole, added 0 holes,
split off 0 statements; this is a proof, not a decomposition. No project module is pruned.
