## What changed

Corrected the false hypothesis of
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffineFree_presheaf_localDual`
in `Sheaf.Paper.CompletedAffineFreePresheafLocalDual`: the section's image under
the sheafification unit must be nonzero. Its conclusion is unchanged. The original
single geometric proof hole remains in this corrected theorem.

Added the proved private certificate `free_presheaf_swap_kernel` in the same
module. For a ringed site and four free generators with two local swap patterns,
it constructs a nonzero free-presheaf section whose sheafification image is zero.
Its proof explicitly evaluates the coefficient of the first generator, computes
both restriction cancellations, and uses naturality and sheaf separatedness.
The construction of the concrete scheme example below is explained in prose;
the private theorem verifies the general conditional cancellation argument.

Adapted the sole direct importer `Sheaf.Paper.CompletedAffineFreeLocalDual`:
case-split on `eta(y)=0` instead of `y=0` after lifting to the free presheaf.
The zero-image branch proves the required local vanishing immediately; the
other branch supplies precisely the corrected hypothesis and gives the same
contradiction with the assumed vanishing of local linear tests. The consumer's
public statement, universes, imports, attributes and instances are unchanged.
The consumer is unclaimed in the shared claim records. The original and adapted
consumer are checked separately against the changed dependency. The original fails
at its application on line 94: `hy0` has type `¬ y = 0`, while the corrected lemma
requires `eta(y) ≠ 0`. The adaptation changes only the case split and its zero
branch; it adds no hypotheses to the consumer. The temporary original-consumer
copy was removed after obtaining this compiler evidence.

Updated both DAG proof records to agree with this argument and recorded the
item's statement correction with its sole citer audit. The change record is
`coord/changes/completed-affine-free-presheaf-nonzero-image.md`. No source-library
module or target statement changes. The blueprint unit route is preserved.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. No split-off theorem or
module was added. This delivery is a correction of a false statement, not a
proof or decomposition of the original false claim.

The one remaining hole is
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffineFree_presheaf_localDual`
(node `lem-sfb-completed-affine-free-local-dual-local-presheaf`), with the
corrected nonzero-image hypothesis and the full geometric proof in its docstring.

The new private `free_presheaf_swap_kernel` is completely proved. The existing
`completedAffineFree_localDual_detect` remains completely proved from the
corrected dependency and sheafification descent, with exactly the original
public signature. Its axioms still include the remaining geometric dependency.

## No longer needed

No import or module is removed, and no module is claimed pruned. No new
geometric obligation is hidden under another name.

The consumer node's old direct proof-dependency entries `sk-def-pe-morphisms`
and `def-pur-twist-coefficient-rings` are no longer part of its assembly proof:
those inputs are encapsulated in the presheaf local-dual lemma. They remain
statement dependencies and are still publicly imported because the unchanged
consumer signature uses them. The consumer now has exactly the two proof
dependencies used by its Lean proof: the corrected local-dual lemma and module
sheafification. No claim is made that the coefficient or pro-affine geometry
is unnecessary to the remaining hole.

## Statement corrected

`completedAffineFree_presheaf_localDual` (node
`lem-sfb-completed-affine-free-local-dual-local-presheaf`): hypothesis `y ≠ 0`
replaced by `eta(y) ≠ 0` (nonzero image under the sheafification unit); the
conclusion is unchanged. Counterexample to the old statement and citer audit:
`coord/changes/completed-affine-free-presheaf-nonzero-image.md` and the node's
`statement_change`. The sole citer `lem-sfb-completed-affine-free-local-dual`
still holds; its Lean proof is adapted in this delivery with unchanged signature.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old statement, repaired): `y ≠ 0` cannot imply nonzero
values under sheaf maps applied to its sheafification image. Free presheaves
on representables need not be separated.

Take `l=2`, `X=Spec(F₂)` and the affine finite étale object `U=W=X ⊔ X`.
The four maps `a=00`, `b=11`, `c=01`, `d=10` from `W` to `U` over `X` are
pairwise distinct. The free section `[a]+[b]-[c]-[d]` has coefficient `1` at
`a`, hence is nonzero (the completed section ring is `Z₂ × Z₂`). On the first
component `a=c` and `b=d`, while on the second `a=d` and `b=c`. The section
therefore vanishes on the two-component cover. Its image in the sheafification
is zero, and every linear sheaf map sends this image to zero. The private
swap-kernel theorem formalizes the general conditional calculation without
assuming injectivity of the sheafification unit.

In particular, the old node's instruction to choose a nonzero equality class
from a nonzero free-presheaf section fails: all local class sums may be zero
even though the global basis coefficients are not. The repaired hypothesis
rules out exactly this obstruction. Empty support and the empty object have
zero sheafification image, so they do not satisfy the repaired hypothesis.
The swap argument works in every coefficient characteristic, including `l=2`;
no distinction between `1` and `-1` is needed for the coefficient at `a`.

The sole DAG citer `lem-sfb-completed-affine-free-local-dual` still holds:
its conclusion concerns a sheafified section, and its proof can test the image
of the local representative directly. The delivered adaptation does this.
No later declaration mentions the changed presheaf lemma directly. The shared
source scan finds 242 transitive importers and only this one direct importer;
the unchanged consumer signature protects the remaining interfaces.

The historical source citation to paragraph (1) of the coefficient blueprint
is also too broad: that paragraph discusses finite free scalar extension and
does not contain the claimed finite-support graph proof. The geometric proof
sketch actually used here is the expanded docstring of
`completedAffineFree_localDual_detect`, identified in the updated proof origin.
The source field is left intact as historical metadata; this discrepancy is
reported rather than represented as a new literature proof.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
