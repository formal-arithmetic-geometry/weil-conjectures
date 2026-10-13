## What changed

Proved `AlgebraicGeometry.square_zero_quotient_local_action` by constructing linear
operators from the uniquely characterized local multiplication sections, then checking
zero, one, addition and multiplication through the injective kernel map. Added the
proof-only imports `Sheaf.Paper.SquareZeroGluedLinearOperators` and
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.square_zero_quotient_local_action`.
Also proved `AlgebraicGeometry.square_zero_glued_linear_operators`.
Added one hole: `AlgebraicGeometry.square_zero_glued_scalar_exists_unique`.
This is a decomposition with net zero holes, not a complete sorry-free proof. The strictly smaller
construction theorem `square_zero_glued_scalar_exists_unique` remains `sorry` in the
new module and is recorded by node `lem-sc-square-zero-glued-scalar-exists-unique`.

## No longer needed

No original import or stated proof dependency was removed. The proof uses the local-lifting theorem and the
sheaf gluing API; no additional planned node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's prose combines existence, uniqueness, gluing, linearity, ring laws and
restriction into one step. Lean proof development shows that the existence and
uniqueness of a scalar section is a separate strictly smaller theorem, so it is split
off as a new node. The item's statement and signature are unchanged.

The initial dry-run preflight required a second-reader section. A temporary
self-review heading was removed; no second reading is claimed. The latest dry run
accepts its absence and reports OK with the second reading pending.
The actual source was read at https://stacks.math.columbia.edu/tag/0B8S because the
local literature/stacks-project/cohomology.tex file is absent.

## New nodes

`lem-sc-square-zero-glued-scalar-exists-unique` states existence and uniqueness of
one scalar-action section in `SquareZeroGluedScalarExistsUnique.lean`; this is the
remaining hole, with the complete local gluing proof in its docstring.

`lem-sc-square-zero-glued-linear-operators` is proved in
`SquareZeroGluedLinearOperators.lean`. Unique scalar sections prove additivity and
scalar linearity in the kernel argument and restriction compatibility. The original
module supplies the separate ring laws in the quotient argument.

Edge cases checked: empty opens have unique sections by sheaf gluing on the empty
cover; I=0 has a unique endomorphism; no assertion that p is surjective on global
sections is used. Data selection uses an existence-and-uniqueness theorem whose
statement determines the chosen section by equality. No change records are needed.

## Second reading by K3

1. Compared `SquareZeroQuotientLocalAction.lean` with the repository version. The
   theorem signature is unchanged byte for byte; only proof code and proof-only
   imports were added.
2. Compiled all three delivered modules with `lcompile.py --all`. They compile
   without errors or warnings. The target proof contains no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`; the sole remaining `sorry`
   is the named split theorem `square_zero_glued_scalar_exists_unique`, with its
   docstring and DAG node.
3. Read both split statements and their nodes. The scalar theorem is the strict
   local existence-and-uniqueness reduction needed by the linear-operator
   theorem; the operator theorem is strictly weaker than the target and states
   exactly the construction used. No duplicate library declaration was found.
4. Checked the proof route and imports. The target uses the linear-operator node,
   which uses the scalar node; `UniqueGluing` is proof-only. The unit route through
   local lifting and gluing is retained, and no unused original import was removed.
5. Checked the DAG `proof`, `proof_deps`, and `proof_origin` against the Lean
   proofs and confirmed the new nodes carry the required metadata. The target
   remains a decomposition: one target hole is closed and one named lower hole
   remains.

Changes made during second reading: none to Lean or DAG content; this section is
the only review edit.
