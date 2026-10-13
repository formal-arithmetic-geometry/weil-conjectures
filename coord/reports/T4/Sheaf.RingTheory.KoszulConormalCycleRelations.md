## What changed

Repaired D1/D2 by removing the equivalent pointwise theorem and its node.
Restored `koszulConormalCycleEvaluation` verbatim to its original module,
removed the pointwise public import and the relocation change record, and
removed the unchanged presentation module from the delivery.

The substantive replacement proves conormal descent explicitly: an alternating
A-multilinear map on I into an A/I-module kills I² in each argument. The proved
private helper `ideal_alternating_descends` constructs an alternating map on
I.Cotangent, checks independence of representatives, additivity, quotient
scalar linearity and alternation. The original theorem then applies the exterior
universal property, compares the chosen Koszul maps with the specified maps by
the existing augmentation homotopy theorem, and proves equality of the two
linear maps on finite sums. The kernel inclusion follows by evaluation at zero.

The only new proof dependency left open constructs alternating products on the
ideal I for one chosen augmentation family, before conormal descent. It contains
no presentation-kernel or arbitrary-family relation-vanishing assertion. The
original node now records exactly this route. Both modules compile locally.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.koszulConormalCycleEvaluation_ker` (node
`new-e1-koszul-conormal-cycle-relations`) by a complete Lean reduction.
`AlgebraicGeometry.ideal_alternating_descends` is proved without sorry.

Added one named hole:
`AlgebraicGeometry.koszul_ideal_alternating_products` (node
`new-t4-koszul-ideal-alternating-products`). Its source and complete construction
in words are in its docstring. This is a decomposition: one original hole
closed and one smaller construction hole added, net zero holes. The delivery
does not claim a completed Tate-product construction or an axiom-free original
theorem. No new definitions or arbitrary witness-based data constructions are
exported; the existence witness is eliminated only inside a proposition proof.

## No longer needed

Removed the rejected delivery's
`Sheaf.RingTheory.KoszulConormalCycleRelationsPointwise` module and
`new-e1-koszul-conormal-cycle-relations-pointwise` node. Removed its public import
and `coord/changes/koszulConormalCycleEvaluation.md`. No original dependency is
pruned: the existing `new-r4-koszul-augmentation-lift-homotopy` is now actually
imported and used. The original presentation public import is retained because
it supplies statement and definition types.

The separate square-ideal-vanishing intermediate considered during repair is
unnecessary: the I-annihilated codomain and multilinearity suffice, and the
private descent proof establishes this directly. No such new module or node
is delivered. The unit has no realized node constraints bypassed here.

## Where the brief, the DAG or earlier work was wrong

The prior pointwise lemma was equivalent to the kernel inclusion, not a strict
reduction. The prior second-reading approval made the same mistake and has been
removed; this repair has not been independently second-read. The evaluation
definition never needed relocation. The new proof implements genuine missing
algebraic descent and comparison steps, leaving only the pre-descent product
construction from original proof steps 1 and 2.

B7 is repaired by removing the rejected node and recording all new searches
as actually returned by msearch.py. LeanSearch returned service unavailable;
its verdict is `unavailable`, without a mathematical no-match claim. LeanFinder,
Loogle and grep ran; their results do not supply this product construction.
The existing self-Tor comparison declarations cannot be imported here because
they depend on this kernel-inclusion module.

Edge cases of the new construction were checked in words: the empty product
in degree zero lies in quotient homology and is killed by I; I=A gives zero
quotient tensor homology; I=0 gives zero positive ideal products. Alternation
comes from strict commutativity, so no invertibility of two is required. The
Lean descent proof treats n=0 without introducing a nonexistent coordinate.

## New nodes

`new-t4-koszul-ideal-alternating-products`, in
`Sheaf.RingTheory.KoszulIdealAlternatingProducts`, isolates alternating products
of ideal elements for a chosen augmentation-preserving family. It asserts no
conormal factorization and no arbitrary-family kernel inclusion. The descent,
exterior extension, comparison and finite-sum argument are proved in the item.
No definition/signature change or forced adaptation is required.

## Second reading by T4

1. **Visible declarations and statements.** Compared the delivered
`KoszulConormalCycleRelations.lean` with the repository version. Existing declaration
signatures, including `koszulConormalCycleEvaluation` and
`koszulConormalCycleEvaluation_ker`, are unchanged byte for byte; the added module
contains only the new split-off theorem recorded by its node.

2. **Proof checks.** Compiled both sandbox modules with `lcompile.py --all`; both
compile cleanly. The original kernel-inclusion hole is closed. The only remaining
`sorry` is the named theorem `koszul_ideal_alternating_products`, with its docstring,
node, and explicit source. No hollow definition, axiom, unsafe, opaque, or extern was
introduced. The closed proof uses the existing augmentation-lift homotopy and the
private conormal descent argument.

3. **Statements and split.** Checked the new theorem against its node and source.
It is a strict lower-level construction: it provides one augmentation-preserving
family and one alternating ideal product before descent, and asserts neither
conormal factorization nor arbitrary-family relation vanishing. The theorem is true
in the stated edge cases (including degree zero, `I = 0`, `I = A`, and characteristic
two) and is not a duplicate found in the library searches.

4. **Pruning and route.** The proof retains the presentation import needed for the
public types and uses the existing homotopy dependency. The rejected equivalent
pointwise theorem, its module, import, node, and change record are removed. No old
proof dependency is silently dropped, and the unit route remains the product,
descent, comparison, and kernel argument recorded in the node.

5. **DAG agreement.** The original node now records the actual proof steps and
`proof_deps`; the new product node records the split theorem, source, proof plan,
searches, and Lean declaration. The delivery is therefore CODEX because it adds the
new module/node and leaves the explicitly documented construction hole.

Changed during this second reading: appended this review section only; no Lean proof
or statement required repair after compilation.
