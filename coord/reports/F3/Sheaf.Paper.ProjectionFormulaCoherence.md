## What changed

Reduced the identity clause `WeilConjectures.sixFunctorProjection_identity` without
changing any existing declaration signature, definition, attribute, or public import.
The proved support module `Sheaf.Paper.ProjectionIdentityAssembly` constructs a
normalized unit by taking the fully faithful preimage
of the inverse identity compositor. Naturality identifies the component of that
unit on an identity pullback with the pullback of the unit component. A second
categorical calculation transports the proper counit identity along the supplied
proper identification to every compactification. Finally, cancellation of the
compositor and naturality prove uniqueness of the unit. Explicit properness
proofs for the identity scheme map avoid repeated instance searches. A generic
normalized-unit-and-property lemma packages existence and uniqueness once; each
coefficient stage supplies only its proper projection calculation. Its four stage
lemmas are proved separately to keep elaboration within the heartbeat budget;
the item combines them using proved private equations for its two existing
comparison definitions, so the kernel can reuse those equations rather than
repeatedly unfold the coefficient-category constructions. The new proof
section respects transparency locally; no shared definition or instance changes.

Finite identity pullback is proved full and faithful directly from
`sfIntrinsicPullbackId`, its derived comparison, and `S.finitePullback`. The two new
modules state strictly separate source steps: fullness and faithfulness
of identity inverse image at the three higher coefficient stages, and the
direct-image proper counit projection identity.
Neither statement contains the original compactification-independent unique-unit
conclusion. Their modules are private proof imports of the proved assembly module; the item
privately imports that assembly module. Both lower statements use
only `SixFunctorOperationDatum`, avoiding an unnecessary import of the additional
six-functor axioms. The item applies them to its underlying operation datum.

## Proved and sorry left

Original holes: 7. One original hole is reduced, six are unchanged, and two lower
holes are added. This is a decomposition, not a complete proof or a net reduction
of the sorry count: closed minus added is -1 at the declaration level. The complete
Lean assembly for
`WeilConjectures.sixFunctorProjection_identity` contains no sorry.

The six original holes left, all attached to `prop-sf-pf-coherence`, are:

- `WeilConjectures.sixFunctorProjection_baseChange_integral`
- `WeilConjectures.sixFunctorProjection_baseChange_rational`
- `WeilConjectures.sixFunctorProjection_baseChange_common`
- `WeilConjectures.sixFunctorProjection_reduction_integral`
- `WeilConjectures.sixFunctorProjection_reduction_rational`
- `WeilConjectures.sixFunctorProjection_reduction_common`

The two new holes are:

- `WeilConjectures.projectionIdentity_pullbackUnits`, node
  `lem-sf-projection-identity-pullback-units`.
- `WeilConjectures.projectionIdentity_properCounit`, node
  `lem-sf-projection-identity-proper-counit`.

The private generic normalized-unit construction, unit uniqueness, and transport
of the identity projection from proper direct image are proved by categorical
cancellation and functoriality. They compile in an isolated check with Mathlib
imports only. The finite full-faithfulness calculation also compiled in isolation
against the actual datum imports.

Validation: the four modules were checked with `lcompile.py --all`; subsequent
profiling identified repeated comparison unfolding in the item. Proved private
comparison equations reduced the diagnostic run from 88 seconds to 53 seconds.
The final packet is submitted to the delivery compile and preflight checks.
No heartbeat or time limit was raised, and no profiling option remains.

## No longer needed

Removed unused private proof imports (none of their declarations is used by a proof
in this file):

- `Sheaf.Paper.CoefficientRealizationTransport`
- `Sheaf.AlgebraicGeometry.ProperCoincidenceNormalized`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.ExchangeFunctoriality`
- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`
- `WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate`
- `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational`

Reviewer correction (stage-3 review, 2026-10-27): the plain imports of
`Sheaf.Paper.ProjectionFiniteReduction` (prop-sf-pf-reduction, realizing the statement of
unit sk-prop-sf-pf-reduction) and `Sheaf.Paper.SfProEtaleProjectionFormula`
(thm-sf-pf-proetale, realizing the statement of unit sk-thm-sf-pf-proetale) are restored.
Both units are used by this unit, the remaining reduction clauses are still `sorry` and their
proof step cites these nodes, and coord/brief-stage3.md §1 keeps such modules imported.

The direct parent dependency on `cor-cbc-proper-coincidence` is unnecessary for
this assembly: its proper transport uses the recorded stage laws. This removes a
direct edge, not the source declaration or any other node’s dependence on it.

The new pullback-unit module also needs only `SixFunctorOperationDatum` in its statement;
it does not import the projection-mate definitions. These are import simplifications,
not module withdrawals. The remaining base-change and reduction obligations retain their existing source plans and DAG dependencies.
The two imports realizing the unit’s own open-square and compactification-pasting
steps are retained. No mathematical node is declared unnecessary for those
unfinished proofs. No source-library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. Profiling exposed an expensive identity
properness search and cumulative elaboration of four stages in one theorem.
Explicit properness proofs and comparison maps, a generic unit wrapper, four
separately proved stage lemmas, and proved equations for the original comparison
definitions address these costs without changing shared definitions or raising a limit. The existing stage laws give proper coincidence
but do not include the normalized identity unit or its proper counit calculation.
The new nodes isolate those two parts of the source's identity sentence. In
particular, existence of an inverse-image identity unit is reduced to fullness and
faithfulness; it is not assumed together with the original projection conclusion.
The proof never infers equality of completed morphisms from separate finite-level
equalities. It requires the integral lower statements on coherent systems before
realization, as their docstrings and nodes specify.

## New nodes

`lem-sf-projection-identity-pullback-units`, in
`lean/Sheaf/Paper/ProjectionIdentityPullbackUnits.lean`, records fullness and
faithfulness of the three higher identity inverse-image functors, with the source
construction through coherent completed systems, rationalization,
and common coefficient fields. There is no chosen data definition or sorry in a
definition.

`lem-sf-projection-identity-proper-counit`, in
`lean/Sheaf/Paper/ProjectionIdentityProperCounit.lean`, records only the proper
direct-image counit calculation at the identity, with a supplied normalized
pullback unit and its right-adjoint uniqueness comparison. It omits support,
compactification parameters and uniqueness. The original module supplies those
parts using the existing proper-coincidence laws and explicit cancellation.

`lem-sf-projection-identity-assembly`, in
`lean/Sheaf/Paper/ProjectionIdentityAssembly.lean`, records four proved declarations:
`WeilConjectures.projectionIdentity_finite`,
`WeilConjectures.projectionIdentity_integral`,
`WeilConjectures.projectionIdentity_rational`, and
`WeilConjectures.projectionIdentity_common`. It constructs and
normalizes the units, proves uniqueness, and transports the proper identity to
compact support. The module has zero holes. Splitting these proved stage lemmas
out of the large item reduces the compilation cost; no original definition moves.

All three nodes belong to the original unit and cite the current blueprint's identity
paragraph. Their sources, proof steps, edge cases, searches, and Lean attachments
are recorded. No existing shared interface changed, so no change record or forced
consumer adaptation is required.

The proper-counit step uses `lem-pur-derived-pullback-tensor-iso` as a tool for
the normalized inverse-image tensor equation. The unit itself has no separate
coefficient-stage tensor-unit statement. The adjunctions and projection-mate
definitions are the same dependencies the original source route already used.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
