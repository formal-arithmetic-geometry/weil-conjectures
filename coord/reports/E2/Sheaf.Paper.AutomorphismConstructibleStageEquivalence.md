## What changed

The proof of `automorphismConstructibleStage_inverse_comparisons` now assembles
integral, rational and common-stage cancellation isomorphisms from the existing
`isomorphismFieldTransport` theorem. A new private proof import,
`Sheaf.Paper.IntegralAutomorphismCancellationNormalization`, supplies the smaller
integral identification needed to match the prescribed compositor/unit formula.
The rational component formulas also prove independence of the finite-stage
transport witnesses, so the common-stage formula uses the same rational family.
No existing signature, definition, instance, exported attribute or public import
changes. Normal transparency handling is restored locally for the final proof,
so the already irreducible rational and common-stage functors stay folded.
The small constructible pullback wrapper is locally reducible there, reversing
an earlier local irreducibility setting only for this assembly.

## Proved and sorry left

One of the four original holes is reduced: the body of
`WeilConjectures.automorphismConstructibleStage_inverse_comparisons` is complete
from the new normalization theorem and the existing field-transport theorem.
One hole is added in the strictly smaller integral equality
`WeilConjectures.integralAutomorphismCancellation_normalization`
(node `lem-sf-integral-automorphism-cancellation-normalization`). The heterogeneous equality retains the two standard presentations of the
same ambient coefficient category and explicitly fixes the compositor/unit
composite to the constructible inclusion presentation. This is a
decomposition, with zero net holes closed, not a completed proof of the integral
normalization argument.

The other three original holes remain unchanged, all on node
`lem-sf-automorphism-constructible-stage-equivalence`:

- `WeilConjectures.automorphismStageQbarSquare_existsUnique`;
- `WeilConjectures.automorphismConstructibleStage_integral_shifts`;
- `WeilConjectures.automorphismConstructibleStage_descended_shifts`.

There are four explicit theorem holes in the delivered files: those three and
the new integral normalization theorem. There is no hole in a definition.

## No longer needed

No existing imports, modules or nodes are pruned. Existing dependencies continue
to support the other clauses and their remaining proof plans. For the completed
inverse-comparisons assembly, separate reconstruction of rational localization
and common-stage descent is unnecessary: the already stated field-transport
theorem supplies them. No source-library declaration is removed or weakened.

## Where the brief, the DAG or earlier work was wrong

The existing inverse-comparisons plan did not expose the equality between its
specified integral compositor/unit cancellation and the epsilon supplied by the
field-transport interface. The new node states exactly this missing integral
step. It does not restate the original all-stage existence assertion. Its proof
must compare entire normalized quotient systems before realization; equality of
finite reductions alone is insufficient. No statement is disputed.

The current item source is present despite its historical quarantine entry.
This delivery preserves its attachment and existing dependencies and does not
withdraw or delete any quarantined source.

## New nodes

`lem-sf-integral-automorphism-cancellation-normalization`, in the new module
`Sheaf.Paper.IntegralAutomorphismCancellationNormalization`, states equality of
two specified integral morphisms for one scheme isomorphism and one object. Its
source is the Weil-structures paragraph and parent proof steps 4--6. Its
natural-language proof uses whole-system normalization, substitution and the
adjunction triangle identity. Identity isomorphisms reduce to that triangle
identity; on zero objects both sides are the unique morphism. This statement
contains neither rational nor common-stage data and is strictly smaller than the
original theorem. The existing nodes `lem-trf-integral-pullback-comparison-realization`,
`lem-weil-isomorphism-derived-pullback-comparison-normalization` and
`lem-pod-pullback-identities-scalar-extension` serve as tools for the specified
normalization; the parent already uses the first two, and the last owns the
epsilon formula that must be identified. No local-unit statement supplies that
identification. No maintainer `tool_uses` approval is added by this worker.
No change record is needed: existing interfaces are unchanged.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
