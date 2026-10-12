## What changed

Proved `AlgebraicGeometry.Etale.upperStarPlusComp_single` in
`Sheaf.AlgebraicGeometry.EtalePullbackSingleComp`, without changing its signature or
visibility. Added seven fully proved private helpers: `single_hom`,
`complex_single_comp`, `derived_single_comp`, `complex_single_natIso`,
`derived_single_natIso`, `plus_single_comp`, and `plus_single_natIso`.
No imports changed. The existing public import is needed by the statement.
The private-helper namespace and variable commands triggered the conservative
static interface check. Their scope and absence of public effects are recorded in
`coord/changes/etale-pullback-single-comp-private-context.md`; no downstream
adaptations are needed.

The complex comparisons agree componentwise for every degree. Their images under
Q satisfy the derived compatibility equations by the existing factorization and
naturality lemmas. The faithful inclusion of bounded-below derived categories
reduces the bounded-below equations to those equations. Cancelling the derived
composition isomorphism and the underived composition isomorphism proves the
requested inverse orientation. The argument is generic in the exact functors and
degree before specialization, so also covers identity morphisms and zero sheaves.
Updated the node's proof and proof_origin to describe this actual route; its
proof_deps remains empty. No unit statement or step is bypassed.

Local compilation passes without warnings. The delivery dry run is the final
compiler and axiom check.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.upperStarPlusComp_single`
(node `lem-sbc-pullback-single-comp`), the item's sole sorry.
Added holes: none. Remaining holes in the delivery: none.
All seven private helpers are proved, with no sorry. This is a proof, not a
reduction to new holed statements.

## No longer needed

Removed imports: none. Pruned nodes and modules: none.
The proof avoids the optional homotopy-quotient intermediate calculation by using
Q's factorization lemmas directly. No corresponding separate node or import was
present to remove. No proof-dependency modules are added.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The original DAG described the
compatibility as elementary but did not supply its Lean glue. The delivery makes
that glue explicit, with composition and natural-isomorphism compatibility
proved separately and transported through the faithful inclusion. Searches using
LeanFinder, Loogle and grep found the single-functor construction and
factorization lemmas, but no pre-existing composite compatibility theorem.

## Second reading by A2

1. Compared the delivered module and node with the repository versions. The public theorem signature and visibility are byte-for-byte unchanged; the only additions are private proof helpers and their scoped context, documented by the existing change record. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles cleanly. Searched for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and `debug.skipKernelTC`; none occur. The proof closes the sole target hole and adds no holes. Verdict: pass.
3. Checked the seven private helper statements and their degreewise/derived reductions. They are true, strictly intermediate, and contain no `sorry`; no duplicate library theorem was found in the recorded searches. Verdict: pass.
4. The proof expands the single-functor factorization, uses the composition and natural-isomorphism factorization laws, and reflects equality through the faithful bounded-below inclusion. The import remains necessary for the theorem statement, and no proof-dependency import is unused. Verdict: pass.
5. Compared the node proof and proof origin with the actual route. The node records the generic single-complex, derived, and bounded-below steps, and the unit route is not bypassed. Verdict: pass.

Changed only this report by recording the second reading; no Lean or DAG repairs were needed.
