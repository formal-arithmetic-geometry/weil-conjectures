## What changed

Replaced the proof of
`AlgebraicGeometry.ProEtale.PrincipalNormalization.principal_cone_tensor_normalization`
in `Sheaf.Paper.PrincipalConeTensorNormalization`. Its signature and all existing public
imports are unchanged. Added private proof imports of
`Sheaf.Algebra.Homology.ReductionIsoShift`, the existing monoidal-unit endomorphism API,
and Mathlib's center-induced linear action API.

The proof identifies the supplied d with the uniformizer in derived_nakayama_resolution,
transports its short exact coefficient sequences through regularPullbackIso, and constructs
κ explicitly as the inverse of the existing canonical reductionIso. Private, proved scalar
helpers identify the prescribed left-unitor scalar action with the monoidal-unit scalar
action. Existing reductionIso naturality, coefficient transition, and inclusion formulas
prove naturality, the quotientStep equation, and the precise finiteUnit equation by
cancellation of isomorphisms. A separate generic signed-shift equation supplies only the
last compatibility clause. The original power and shift structures are preserved.

Added `Sheaf.Algebra.Homology.ReductionIsoShift` with one strictly smaller obligation:
compatibility with an integer shift of the fixed, already constructed reductionIso for
one short exact principal sequence in a general monoidal abelian category. It contains
no coefficient tower, no sheaf normalization, no construction or existence of κ, and no
transition or unit equations. Its docstring and node give the chain-level sign argument
and its localization. Updated the original node's proof route and proof dependencies.
No source-library files, definitions, existing statements, unit records, or consumers
were changed. No change record or forced adaptation is required.

## Proved and sorry left

Original item: one hole. Closed the hole in
`AlgebraicGeometry.ProEtale.PrincipalNormalization.principal_cone_tensor_normalization`
(node `lem-pe-principal-cone-tensor-normalization`) by a complete Lean proof from named
declarations. The item module now has zero sorries, and its private helpers are proved.

Added one hole, and this is the delivery's only remaining sorry:
`DerivedCategory.reductionIso_inv_signed_shift` in
`Sheaf.Algebra.Homology.ReductionIsoShift`
(node `lem-pe-reduction-iso-signed-shift`). This is a decomposition, with one hole closed
and one added, net zero; it is not a complete axiom-free proof of normalization.
The natural-isomorphism construction, its naturality, coefficient exactness transport,
quotient transition, and cone-inclusion/tensor-unit formula are proved without this new
lemma; only the final shift conjunct uses it.

Both modules compiled together through lcompile.py. The final warning cleanup removes
unused section assumptions from the private single_map helper; delivery recompiles the
packet. The parent theorem's signature was checked byte-for-byte against the source.

## No longer needed

No existing imports were removed, and no modules are withdrawn or claimed globally
prunable. The original direct proof dependency on `lem-pe-scalar-cone-tensor-model`
(`Sheaf.Algebra.Homology.ScalarConeTensorModel`) is unnecessary for assembling this parent:
upstream TensorMappingCone already provides reductionIso and its naturality, transition,
and unit formulas. The new shift node still depends on the scalar-cone model's mathematics,
so this is only removal of a direct parent edge, not global pruning of that node or module.
The target and unit route through derived Nakayama resolution is retained.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or tool failure. The old plan need not reconstruct the cone/tensor
comparison or separately prove its naturality: the adopted source library already proves
those results, including normalized transitions and inclusion. The additional signed-shift
identity for that fixed comparison was not found among the stated dependency declarations,
Mathlib searches, or project source searches. It is isolated as precisely that last equation,
not the original normalization obligation under a new name. The zero complex, arbitrary
integer shifts, and unbounded inputs impose no extra hypotheses; coefficient short exactness
is retained in the new lemma.

## New nodes

`lem-pe-reduction-iso-signed-shift`, in
`dag/nodes/sec-proetale-coefficients/lem-pe-reduction-iso-signed-shift.json`, realizes
`DerivedCategory.reductionIso_inv_signed_shift`. It records the blueprint resolution and
first-reduction cone paragraphs, the signed total-tensor component argument, the K-flat
localization/counit shift square, all proof dependencies, three kinds of completed search,
and the full Lean statement. This is the final shift clause for a canonical comparison
for one coefficient sequence, strictly part of the parent argument. No change records.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
