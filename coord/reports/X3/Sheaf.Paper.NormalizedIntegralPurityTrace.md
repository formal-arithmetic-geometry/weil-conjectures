## What changed

Preserved the already-landed coefficient projection identity `quotientProjection` and its
private quotient tower and naturality argument. Its simplification and rewrite steps
are adjusted for enabled transparency checking. No credit is claimed for that
existing result.
Reduced `normalizedIntegralPurityTrace` to two strictly smaller, canonical comparison
statements: the three comparison cocycles and the exceptional counit reduction.
The parent proof supplies the residue Tor assertion, finite-Tor membership, support
comparison invertibility, the specified forward purity square, inverse square by
cancellation, the actual trace calculation by naturality, and every further finite
purity/inverse/trace/counit equation. No existing declaration signature or definition
body changes. New proof helpers are private and completely proved. Local irreducibility
of the intrinsic realization, derived tensor and coefficient constructions prevents costly
repeated unfolding; no global attribute or definition body is changed. The trace
algebra is proved once in a generic private helper and instantiated at the actual maps.

The two new modules have public imports only for their statement vocabulary. Their
interfaces take the named comparison maps with explicit equations fixing them to the
canonical tensor associator, support comparison and counit. The parent supplies each
normalization equation by reflexivity after unfolding the named definition. This
avoids expensive repeated matching of expanded maps. The new modules import no
parent and create no cycle. The parent imports them privately.

## Proved and sorry left

Original holes closed (1):

- `WeilConjectures.NormalizedIntegralPurityTrace.normalizedIntegralPurityTrace`
  (decomposed, with a complete combining proof).

New holes added (2), each exactly a public named theorem with source, proof in words,
and a matching DAG node:

- `WeilConjectures.NormalizedIntegralPurityTrace.integralPurityComparisonCocycles`,
  node `lem-sf-integral-purity-comparison-cocycles`.
- `WeilConjectures.NormalizedIntegralPurityTrace.integralPurityCounitReduction`,
  node `lem-sf-integral-purity-counit-reduction`.

No holes remain in the assigned module. This is one decomposition into two residual
comparison obligations, with net minus one holes. It is not a complete mathematical proof. Both split
statements include equality levels, zero objects and empty schemes; neither asserts
uniqueness of arbitrary integral lifts. No data are chosen from either new theorem.

## No longer needed

The old route's dimension-bound argument is unnecessary for support comparison
invertibility: the existing `PurCompactSupport.reductionComparison_isIso` applies
directly to the uniform finite-Tor source and target given by reconstruction.
The obsolete tool-use approvals for `lem-kun-dimension-finite-type` and
`lem-pur-adic-source-finiteness-reductions` are removed. The source-finiteness
normalization remains a dependency of the new cocycle statement, rather than a
direct call from the parent.
Accordingly the parent no longer directly uses `lem-kun-dimension-finite-type`,
`lem-coef-integral-compact-support`, `prop-coef-integral-exceptional-adjoint`, or
`lem-coef-finite-exceptional`. The last two and integral support remain in the proof
plans of the new comparison statements; they are not claimed globally pruned.
The ordinary finite exceptional theorem is unnecessary for the finite counit
identity: `existsUnique_finiteReductionExceptionalComparison.choose_spec.1` already
states that identity for the exact finite comparison used here.

Imports removed from the parent:
`Sheaf.Paper.IntegralCompactSupportPrescribedReductions`,
`WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
`Sheaf.SixFunctors.FiniteExceptional`.
Their direct proof calls are replaced by the existing comparison API or the two
precise comparison obligations; no existing public import is changed.
No module is withdrawn. The unit route remains the integral reconstruction,
canonical coefficient comparisons and finite purity/trace route.

## Where the brief, the DAG or earlier work was wrong

The recorded exceptional-adjoint dependency attaches to an etale coefficient module;
its signature does not directly give the reconstruction-coordinate target cocycle or
the transported counit equation. Similarly the source finiteness theorem expresses
its quotient cocycle using `purAdicQuotientNormalization`, while this parent uses the
actual tensor associator `reductionComposition`. The new cocycle statement records
that coordinate identification without silently treating the two as definitional.

The completed quotient transition is a consecutive-quotient sequence; direct quotient
maps are identified by naturality against the direct quotient diagram before applying
the limit cone equation. A bare definitional equality would not establish this.

## New nodes

`lem-sf-integral-purity-comparison-cocycles` / `Sheaf.Paper.IntegralPurityComparisonCocycles`:
the source, exceptional and support cocycles after the canonical tensor associators.
This is precisely parent step 6's comparison portion, with no purity, inverse or trace
conclusion. Its hypothesis is the already-proved projection equality retained in the
parent. It uses the existing source, exceptional and compact-support normalizations.

`lem-sf-integral-purity-counit-reduction` / `Sheaf.Paper.IntegralPurityCounitReduction`:
only the actual transported counit's finite reduction equation, parent step 2's final
equation. No purity or trace equation is assumed or concluded. The parent's genuine
naturality calculation derives the trace equation from this and the forward square.

Both nodes cite clause (6) of the current blueprint and contain the full normalization
argument in their proof and Lean docstring. LeanSearch, LeanFinder and Mathlib grep
found generic derived-adjunction identities, but no theorem for these specific
completed and finite coefficient realization maps. No change record is needed:
existing signatures, public imports and definitions are preserved.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
