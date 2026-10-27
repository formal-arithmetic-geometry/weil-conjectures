## What changed

Replaced the hole in `WeilConjectures.constantExtensionSheetGeometry` by a construction
of all ten fields of the unchanged `ZlSheetGeometry` interface. The open sets are the
actual ranges of the prescribed cyclic maps; their coordinates are the canonical
`IsOpenImmersion.isoOfRangeEq` isomorphisms. The proof establishes open and closed
immersion properties using the étale separated projection, proves successor and cyclic
return identities, and reuses the existing new-model Frobenius identity.

Added `Sheaf.Paper.ConstantExtensionSheetTensorSplitting` with a complete proof of
`WeilConjectures.constantExtensionSheetTensorSplitting`. The canonical evaluation map
is surjective by independence of embeddings; equal finite dimensions give injectivity,
and the actual finite-field cardinalities give the degree and embedding count m.

Added `Sheaf.Paper.ConstantExtensionCyclicSheetPartition`, isolating only the point-set
partition assertion still needed to finish the geometric argument. This asserts no
immersion, coordinate, tensor, or normalized Frobenius identities. The item combines
this strictly smaller statement with the preceding proved results.

No existing signature, definition, target, or consumer interface changes. The unit's
route is preserved. No source-library file is edited. Remote `lcompile.py --all`
compiled all three delivery modules successfully (52.1 s, 59.9 s, 53.7 s); delivery
preflight is run by `deliver3.py`.

## Proved and sorry left

Original holes: 1, `WeilConjectures.constantExtensionSheetGeometry`.
Its body now has no hole and constructs the unchanged package from the strictly smaller
point-partition statement and complete proofs of the other clauses. This is a decomposition,
not a net proof: 1 original hole closed, 1 new hole added, net 0.

The proved new public theorem `WeilConjectures.constantExtensionSheetTensorSplitting`
has zero holes. The private positive-power, successor, return and immersion helpers
have zero holes.

The only sorry left in the delivery is
`WeilConjectures.constantExtensionCyclicSheetPartition`, node
`lem-zl-constant-extension-cyclic-sheet-partition`. Its source and complete semilinear
component argument are in its docstring and node. The cases m=1 and empty X_0 are
included: disjointness is vacuous in the first case; all ranges and the ambient space
are empty in the second. Repeated or absent labels would be incorrect, which is why the
remaining proof explicitly uses the finite-field Frobenius bijection.

## No longer needed

Removed the item's private import
`WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorCoproduct`, and removed
`lem-exc-finite-galois-algebra-tensor-decomposition` from its proof dependencies.
Dedekind independence proves exactly the required tensor evaluation map directly,
without first constructing the tensor square over the finite extension and then
extending scalars. The adopted source declarations remain untouched.

Removed the item's private import `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`.
That module and node `lem-weil-pbc-spec-finite-product-fields` are still needed in the
point-partition lemma's proof plan. The new module imports only the public interface its
statement needs; a later proof imports the lemmas it actually uses. No global pruning
of this dependency is proposed.
Likewise `lem-weil-pbc-fibre-product-affine-spectra` is needed only by that remaining
step. The finite-field Frobenius facts and Frobenius definitions remain in use.
No other module or node is proposed for withdrawal.

## Where the brief, the DAG or earlier work was wrong

`finiteGaloisTensorCoproduct`, the declaration attached to the original tensor
coproduct dependency, takes the tensor algebra equivalence and its formula as hypotheses.
It does not by itself supply the evaluation splitting demanded by the geometry package.
The separate source file `FiniteGaloisTensorDecomposition` contains a proved private
Dedekind-independence argument; this delivery specializes that proof pattern to
k tensor k_m and embeddings into k, avoiding the unnecessary scalar-extension step.

The original plan also repeats the sheet-return and new-model Frobenius calculations,
but `constantExtensionSheet_return` and `constantExtensionFiber_return` are already
proved in `ConstantExtensionWeilHeartData`. The delivery reuses them. The complete
geometry theorem `constantExtensionCyclicSheets` cannot be used here: its current proof
imports and applies this assigned item, so that route would be circular.

## New nodes

`lem-zl-constant-extension-sheet-tensor-splitting`: the prescribed tensor formula and
embedding count, proved in its own module by independence and dimension. Searches used
LeanSearch, LeanFinder, Loogle and local Mathlib/source/DAG searches. The generic
separable-tensor theorem lacks the prescribed evaluation formula; the finite Galois
private proof has a different tensor domain and index set.

`lem-zl-constant-extension-cyclic-sheet-partition`: pairwise disjointness and union of
the actual cyclic-sheet ranges, the remaining topological part of the original
argument. It follows Deligne's disjoint-union description on p. 152, with the geometric
Frobenius convention of (1.1.7). LeanSearch and LeanFinder found only field-level
Frobenius enumeration; project and blueprint searches found no independent duplicate.
No change record is required: these are new theorem statements, with no changes to an
existing statement or definition.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
