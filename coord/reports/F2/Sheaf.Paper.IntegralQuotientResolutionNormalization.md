## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralQuotient.integral_quotient_resolution_normalization`
in `Sheaf.Paper.IntegralQuotientResolutionNormalization`, preserving its entire statement,
all five existing abbreviations, and all public imports. Added proved private glue only.

The proof establishes the scalar exact sequence, checks the actual continuous condensed
coefficient sequence on profinite sections, and pulls it back exactly. It reconstructs the
normalized integral ring comparison from the existing integral-limit theorem and finite
encodings. An explicit ULift quotient equivalence identifies the adic constant tower and
its scalar maps with the recorded completion; the completed-constant-algebra theorem then
supplies flatness. The original cone has two flat regular terms. Existing bounded-flat
criteria give both K-flatness assertions. Mathlib's short-exact cone augmentation supplies
the specified map and its quasi-isomorphism; the exact section equivalence preserves it.

Validation: the complete module compiled without errors or warnings through `lcompile.py`
in 52.9 seconds, under the normal 60-second limit and unchanged heartbeat budget.

Updated the existing node's proof, proof dependencies and proof origin to this route.
No public definition, target signature, source-library declaration, or consumer changes.
The current rework ledger names a quarantine caused by a transitive import build failure;
the module's mathematical declarations and Lean attachment are preserved in this delivery.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.IntegralQuotient.integral_quotient_resolution_normalization`
(node `lem-sfb-integral-quotient-resolution-normalization`).

Remaining holes in the item: 0. Added holes: 0. Split-off statements: 0.
Every private theorem is proved, and every private definition is an explicit construction.
Chosen finite encodings and the integral comparison are fixed by their stated normalization;
no arbitrary object is extracted from an unproved mere existence statement.

## No longer needed

Removed the unused private imports `Mathlib.Topology.Algebra.Valued.LocallyCompact`,
`Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding`,
`Sheaf.Paper.ConstantCompletionEquivalence`,
`Sheaf.Algebra.Homology.FlatScalarCyclicResolution`, and
`Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat`.

The proof does not use `lem-sfb-flat-scalar-cyclic-resolution`
(`Sheaf.Algebra.Homology.FlatScalarCyclicResolution`): sectionwise cancellation and continuous
uniformizer division prove monicity and exactness for the actual maps directly.

It does not use `lem-sfb-finite-free-mono-cokernel-kflat`
(`Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat`): the cone decomposition, unit flatness,
bounded-flat criteria and Mathlib's canonical augmentation suffice directly.

It does not use `lem-weil-pbc-pid-noetherian-normal`: the DVR theorem supplies a PID instance,
and Mathlib infers Noetherianity without the other normality assertions of that node.

It does not directly use `lem-weil-pbc-constant-completion-equivalence`
(`Sheaf.Paper.ConstantCompletionEquivalence`): it uses the already proved arbitrary-universe
`lem-weil-pbc-completed-constant-algebra-flat-quotients` specialization instead. The former
remains a transitive dependency of that theorem, so this is no whole-library withdrawal.

It does not use the integral `Encoding` structure from
`def-pe-integral-presentation-encoding`; instead it constructs only the required normalized
ring comparison. Its module remains publicly imported by the normalized-restriction-square
module, whose reconstruction and unit helpers the proof uses. That dependency therefore
cannot be globally pruned by this delivery.

Removed obsolete top-level tool approvals for the direct constant-completion, cyclic-resolution
and finite-free-cokernel steps. Retained all other existing approvals in their original order.
New route tools are the integral-limit comparison, continuous uniformizer division, completed
constant algebra flatness, and independent-universe bounded-flat criterion; these supply only
generic coefficient constructions below the proper-base-change unit, whose route is preserved.
No module is withdrawn, and no claim is made that the named modules have no other consumers.

## Where the brief, the DAG or earlier work was wrong

The previous route described the older integral presentation using its absolute-value topology.
The item's actual coefficients use the spectral topology. The proof explicitly transports the
topology for continuous division and proves projection normalization for the actual reduction,
so it neither replaces the coefficient object nor assumes these maps are definitionally equal.

The generic completed-constant theorem at equal site universes does not apply directly to the
small pro-etale site. The existing arbitrary-universe completed-constant-algebra theorem does;
the proof supplies its precise scalar and finite-projection hypotheses through the constructed
quotient-tower isomorphism.

The generic internal closed-category and concrete section-equivalence constructions are
expensive to unfold during instance comparison. Local irreducibility and proved private
flatness/augmentation bridges keep the unchanged categorical constructions abstract;
no heartbeat or wall-clock limit is raised. The standard degree-zero single functor's finite
limit and colimit instances are supplied explicitly through `HomologicalComplex.single`.
The cone augmentation helper takes the caller's zero-object and binary-biproduct instances
explicitly; deriving fresh choices from its abelian assumption caused expensive comparison
against the actual module-category cone. Sharing these choices resolves the timeout.

A whole-DAG traversal also found a pre-existing cycle below constant-completion's
ring-complex dependencies: `lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent` cite each other. This delivery
changes neither node. No proposed proof dependency reaches this item, so the route
introduces no cycle; Lean import-direction checks for the added imports also pass.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
