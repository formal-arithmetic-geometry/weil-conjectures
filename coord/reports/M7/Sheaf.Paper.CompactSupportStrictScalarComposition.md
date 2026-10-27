## What changed

In `Sheaf.Paper.CompactSupportStrictScalarComposition`, prove
`WeilConjectures.PurStrictScalar.compactSupportCompletedScalarIdentity` from the existing
completed composition equation, naturality, and the invertibility supplied by
`compactSupportScalarLimitReduction`. Move the already proved naturality theorem before
the identity theorem so it can be used there, explicitly unfolding its uniquely
specified comparison only when applying the normalization equation. Private proved
helpers identify the normalized completed tensor associator for two identity
embeddings with scalar extension of the tensor unit. A small proved interface extracts
finite-Tor preservation and invertibility for arbitrary coefficient maps before the identity specialization.
The helpers use exact localization coherence and Mathlib's
`Adjunction.leftAdjointCompIso_id_comp`.

Add the private proof import `Mathlib.CategoryTheory.Adjunction.CompositionIso`.
Update the existing node's proof and proof origin to record this shorter argument.
Local irreducibility keeps completed coefficient and derived constructions folded during
proof elaboration. A private categorical lemma combines the composition and
naturality equations by cancellation and faithfulness of scalar extension, which is
isomorphic to the identity. It accepts only morphisms in the target category,
avoiding expensive conversions between presentations of the source and support
functors. Existing public statements, defining expressions, instance choices, and
public imports are preserved. The completed module compiled on the server in
33.2 seconds before removal of profiling output.

## Proved and sorry left

Closed one of the six original holes:
`WeilConjectures.PurStrictScalar.compactSupportCompletedScalarIdentity`.
No holes are added or split off. This is a proof from the existing composition and
scalar-limit-reduction declarations; it is not a claim that their remaining dependencies
are already sorry-free.

The five remaining holes all belong to
`lem-pur-compact-support-strict-scalar-composition` and retain their existing source and
complete proof plans:

- `WeilConjectures.PurStrictScalar.compositionProper`.
- `WeilConjectures.PurStrictScalar.compositionOpen`.
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarComposition`.
- `WeilConjectures.PurStrictScalar.compactSupportScalarLimitComposition`.
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarIdentity`.

## No longer needed

No import, node, or module is pruned: the remaining strict, geometric, and Roos clauses
still require their recorded dependencies. The completed identity clause itself no
longer needs a separate derivation from strict identity, the identity cofinal map,
or the completion unit square: normalized associator unitality, completed composition,
naturality, invertibility, and faithfulness suffice. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original completed-identity plan is longer than needed:
the invertible composition law already forces its unit law after identifying the tensor
associator's left unit. The revised node records that argument. The finite-Tor condition
for the scalar-extended input and invertibility of the comparison are both extracted
from the existing scalar-limit-reduction theorem, not assumed separately.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
