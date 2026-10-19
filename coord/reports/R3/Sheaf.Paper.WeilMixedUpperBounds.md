## What changed

Filled the six original proofs in `Sheaf.Paper.WeilMixedUpperBounds`, preserving
all existing public signatures and definitions. The truncation comparisons are
extracted from `constructibleTruncations_exists`, using uniqueness of the recorded
standard t-structure and subsingleton residue-field inverse structures. Cohomology
belongs to the heart by the two truncation bounds and their shift formulas.

For mixedness, identify the recorded finite filtration with the already proved
`ObjectProperty.filtrationClosure` API. Prove isomorphism closure directly from
finite Weil presentations. Prove pure subobject and quotient closure using exact
Frobenius fibres and the proved source eigenvalue-transfer lemmas; then use the
generic subobject, quotient and extension closure results. In particular the
extension proof is complete and uses the canonical short exact cokernel sequence.

Added proof-only imports of
`WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions`,
`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map`, and
`Sheaf.Paper.PunctualSpectrumExactFibre`. Added the latter module to isolate the
coefficient-normalization bridge, with a full source proof in words and a node.
Updated the original node's proof, proof dependencies and proof origin to match.
No existing definition or statement changed, and no consumer adaptation is needed.

## Proved and sorry left

Closed the six original holes (full namespace `WeilConjectures`):

- `sfWeilFrobeniusTruncLE_existsUnique`.
- `sfWeilFrobeniusTruncGE_existsUnique`.
- `sfWeilCohomology_mem`.
- `SfIsMixedOfWeightsAtMost.of_mono`.
- `SfIsMixedOfWeightsAtMost.of_epi`.
- `SfIsMixedOfWeightsAtMost.of_mono_cokernel`.

The original module has zero remaining holes. Four closures use existing
interfaces directly. The subobject and quotient arguments are complete Lean
reductions through one separate exact-spectrum result; they are not claimed as
independent proofs of that result.

Added one hole: `WeilConjectures.sfPunctualSpectrumExactFibre`, node
`lem-zl-punctual-spectrum-exact-fibre`, in
`Sheaf.Paper.PunctualSpectrumExactFibre`. This is a decomposition: six old holes
closed, one new hole, net five before the ledger's import-closure accounting.
There are no holes in definitions or private helpers. The new theorem's witness
is used only inside proofs, never to choose an object in a public definition.

Both delivered modules compiled through `lcompile.py --all`; the final clean
verification and delivery preflight are recorded by the delivery tool. The fibre
lemma was checked mathematically on zero fibres, empty schemes, nonminimal finite
coefficient presentations, independent universes and nonseparated finite-type
schemes. In the last case exactness is local on an affine neighbourhood defined
over the finite field, which is Frobenius-stable after base change.

## No longer needed

No original imports, nodes or modules are pruned. The original three public
imports retain the interfaces required by the unchanged definitions. All three
new proof-only imports are used. No numbered unit step is bypassed: the unit has
no separately realized proof steps, and the closure argument follows its stated
intersection/image/splicing route via the existing generic filtration theorem.

The proof does not import the analogous source-model sheaf closure theorems in
`WeilConjectures.DeligneLaumon.Reduction.Weights`, because they concern a different
Weil category. Nor does it add the separated, single-universe
`Sheaf.Paper.RationalStalkExact` as an unused dependency. These were alternatives
examined, not original dependencies removed.

## Where the brief, the DAG or earlier work was wrong

The original node had an empty proof despite the six admitted theorem proofs in
its module. The existing truncation package already gives the two uniquely
normalized comparisons, so rebuilding t-exact adjunctions is unnecessary.

The generic filtration closure instance alone does not prove the subobject and
quotient clauses: its pure object property must first be shown closed under
subobjects and quotients. This needs a bridge from `SfPunctualEigenvalue`, which
quantifies over all finite Weil presentations, to exact Frobenius fibres in the
actual common-stage heart. `wfRationalStalkExact` does not state that comparison;
it also assumes separatedness and identifies the coefficient universe with the
scheme universe. `sfAdicCommonFiber_exists` supplies normalized intrinsic fibres
but its conclusion alone does not provide the exactness and natural local
Frobenius/spectrum assertions needed here. These are formal interface gaps, not
objections to using existing admitted dependencies.

## New nodes

`lem-zl-punctual-spectrum-exact-fibre` states the exact finite-dimensional
Frobenius fibre and its agreement with the finite-presentation spectrum. It has
no weights or mixed filtration hypothesis, so is a separate local coefficient
result, not a renamed mixedness-closure statement. Its proof in words uses
BS 6.8.5, 6.8.7, 6.8.14 and 6.8.15, normalized intrinsic coefficient fibres,
common-stage finite-diagram descent, natural point transport, scalar-compatible
pullback comparisons and independence of the residue embedding. The source
argument is the exact Frobenius-fibre part of the subquotient closure sentence.

Blueprint searches for `exact Frobenius fibre` (no match) and `punctual` were
performed; the lisse subquotient-purity node has stronger hypotheses and is a
weight statement, while the rational-stalk exactness node lacks the required
normalization comparison. The point-transport invertibility input is recorded
explicitly in the new node; it is applied to the separated auxiliary point model,
independently of Y0.
Three kinds of Mathlib searches are recorded in the
new node and `searches.jsonl`. No change record is required because no existing
signature, definition or statement changed.

The coefficient-fibre and Frobenius transport nodes from other units are used as
tools for this local comparison; the mixedness unit itself only gives the closure
sentence, not the normalized fibre construction. No `tool_uses` field is added.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
