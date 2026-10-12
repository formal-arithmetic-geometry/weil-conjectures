## What changed

Replaced the sorry in `Field.matrixDescentScalarMap_bijective` by a complete Lean
proof combining the base-change basis of the invariant algebra, independence of
its images, and their span. Its signature and public imports are unchanged.
Added proof imports of `MatrixDescentInvariantsLinearIndependent`,
`MatrixDescentInvariantsSpan`, and `Mathlib.LinearAlgebra.TensorProduct.Basis`.
The two new modules each state one theorem and have matching DAG nodes.

`Field.matrixDescentInvariants_linearIndependent` is fully proved by finite-set
induction. Applying twisted conjugation to a finite expansion and comparing
coefficients forces them into K, contradicting K-linear independence. This
argument needs no local constancy or action laws. The original node now follows
the actual proof: choose a K-basis first, prove its independence over the
separable closure, identify its span, and apply the tensor-product basis lemma.
The unit route is unchanged; no realized unit step is bypassed.

## Proved and sorry left

Closed the original hole in `Field.matrixDescentScalarMap_bijective`
(node `lem-sc-matrix-descent-scalar-map-bijective`), conditionally on the spanning
statement below. The item's module now has zero direct sorries.

Also fully proved `Field.matrixDescentInvariants_linearIndependent`
(node `lem-sc-matrix-descent-invariants-linear-independent`). Its proof uses
only the already proved invariant-algebra definition and Mathlib.

Added exactly one hole: `Field.matrixDescentInvariants_span`
(node `lem-sc-matrix-descent-invariants-span`, module
`Sheaf.FieldTheory.MatrixDescentInvariantsSpan`). This is the spanning conclusion
of original steps 1--3, not a restatement of scalar-map bijectivity. Its docstring
and node give the finite Galois reduction and weighted invariant-sum proof.

This delivery is a decomposition: one original hole closed and one spanning hole
added, net zero holes. The injectivity and tensor-basis combination are now fully
formalized. All three modules compile. Edge cases were checked mathematically:
n=0 gives the zero matrix space and an empty independent family; n=1 gives the
base field as invariants; characteristic dividing the finite group order causes
no problem because the proof uses unnormalized sums, never division by its order.

## No longer needed

No existing dependency imports, nodes or modules are pruned. The sole original
proof dependency `def-sc-matrix-descent-invariants` remains necessary. The
combining proof does not construct an L-basis or a finite-extension tensor
isomorphism: it works with an arbitrary K-basis of A_b and its base change to the
separable closure. Those prose constructions had no separate dependency modules.
Every added proof import is used.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan had no named dependencies for
its finite Galois descent steps, so the spanning conclusion is now an explicit
public theorem available for the next worker. Tag 03R6 provides the twisting
classification sketch; the detailed spanning and coefficient arguments are the
project's agent-expanded descent proof, as the new source records specify.

`blueprint_refs.py ancestor` reports None for the item because the `created.item`
chain contains module names. New nodes instead use the documented ancestor
`lem-sc-brauer-zero` from the BrauerScalarDefectSurjective node and list the
intervening mathematical nodes. Searches across the imported blueprint for
invariant, descent and 03R6 found no equivalent statement. LeanSearch returned
an Internal Server Error; this is recorded as unavailable, not as a negative
search result. No existing declarations or definitions were changed.

## New nodes

`lem-sc-matrix-descent-invariants-linear-independent` records the fully proved
independence theorem, with no continuity or action hypotheses. Its source is
the coefficient uniqueness argument in original step 4. Finite-set induction,
semilinearity of conjugation, and the separable-closure fixed-field theorem are
formalized directly. Empty families and n=0 are included.

`lem-sc-matrix-descent-invariants-span` records the remaining spanning theorem,
with the exact local-constancy, identity and composition hypotheses of the
original item. Original steps 1--3 and extension via matrix units supply its
complete natural-language proof. It is strictly the surjectivity part of the
argument. Searches found related Krull-topology and orbit-span facts but no
semilinear invariant spanning theorem. No change record is needed: every
existing signature, definition and public import is preserved.

## Second reading by X3

1. **Statements and accidental changes.** Compared the delivered scalar-map module with the repository version. The target signature and all existing declarations are byte-for-byte unchanged; only proof imports and the target proof body were added. The two new theorem statements are separate independence and spanning claims and do not restate the target.

2. **Proof and axioms.** Compiled all three sandbox modules with `lcompile.py --all`. The scalar-map proof compiles and has no direct `sorry`; the independence theorem has no `sorryAx` and depends only on `propext`, `Classical.choice`, and `Quot.sound`. The spanning theorem is the single documented split-off `sorry`, so the scalar-map theorem transitively reports `sorryAx` as expected.

3. **New statements and sources.** Checked the new declarations against their docstrings and DAG nodes. The independence statement is strictly the coefficient-uniqueness component; the span statement is strictly the surjectivity component. Both include edge cases such as empty index sets and `n = 0`, and searches recorded in their nodes found no existing Mathlib or library duplicate.

4. **Route and pruning.** The scalar-map proof follows the unit route: choose a basis of the invariant algebra, use base change, independence, and spanning, then apply the tensor-product basis bijectivity lemma. All proof-only imports are plain `import`; public imports remain those required by the statements. No old proof dependency became unused, so no pruning was needed.

5. **DAG consistency.** Verified that the target node lists both new lemmas in `proof_deps` and that each new node's Lean declaration, statement, source, and proof route match the delivered modules. The unit's realized route is preserved.

No further changes were needed in this second reading.
