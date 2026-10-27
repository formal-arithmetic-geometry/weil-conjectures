## What changed

Proved `WeilConjectures.sixFunctorProjection_reduction_finite` in
`Sheaf.Paper.ProjectionFormulaCoherence`, with its existing signature unchanged.
The proof cancels the actual component's source and target realization comparisons,
uses the realization equivalence's fully faithful preimage equation, and applies the
existing compactification tensor-action identity to the degree-zero constant quotient A/J.
The conjugation defining `sixFunctorProjectionFiniteInFixedCoordinates` is unchanged.

The finite square uses the same derived tensors, support functor, inverse image and
associators through their canonical presentations. Its equation is constructed in a local
generic coefficient-category function before specializing coefficients, avoiding repeated
large conversions in the concrete presentation. Its lower components use the existing
`projectionTensorCoordinateComponent` and its proved equality to the published projection.
The named `projectionActionAssociator` is the canonical tensor associator. The ideal remains
arbitrary; the ambient lower projection retains reductions outside the finite-Tor domain.

`Sheaf.Paper.ConstructibleProjectionMates` is not changed (reviewer, 2026-10-26). The
delivery had restated `fixedDerivedPull` through a local generic function. The item compiles
against the published module in about 44 s, so that adaptation was not needed and was
withdrawn. Its record `coord/changes/V5-fixed-derived-pull-braiding.md` is marked withdrawn.

`FiniteProjectionActionLaws` becomes a public import because the square uses its named
associator. Private import-all commands expose its already-proved general action theorem
and the three stored coefficient property proofs used only in a private coordinate lemma.
That lemma explicitly identifies the Grothendieck, monoidal-additivity and flat-resolution
proof arguments before reflexivity. No private helper enters a public signature or
public definition body. All new proof scopes respect transparency; no limits are raised.
There are no new public declarations or new nodes, and no source-library file is edited.

The definition-presentation change of the square and its consumers are recorded in
`coord/changes/V5-projection-coherence-proof-scopes.md`. The owning node records the actual
realization cancellation and tensor-action argument. Existing unit statements and routes,
including the open/base-change and compactification-pasting steps, are retained.

## Proved and sorry left

Closed one of the nine initial holes:
`WeilConjectures.sixFunctorProjection_reduction_finite` (prop-sf-pf-coherence).
No holes added and no statements split off. The imported general tensor-action theorem
retains its original complete proof. Its axioms include `sorryAx` only through the existing
realization comparisons and `sixFunctorProjection_realization`, which still depend on
unfinished statements.

The following eight holes remain unchanged, all attached to prop-sf-pf-coherence:

- `WeilConjectures.sixFunctorProjection_baseChange_integral`
- `WeilConjectures.sixFunctorProjection_baseChange_rational`
- `WeilConjectures.sixFunctorProjection_baseChange_common`
- `WeilConjectures.sixFunctorProjection_identity`
- `WeilConjectures.sixFunctorProjection_baseChange_finite`
- `WeilConjectures.sixFunctorProjection_reduction_integral`
- `WeilConjectures.sixFunctorProjection_reduction_rational`
- `WeilConjectures.sixFunctorProjection_reduction_common`

## No longer needed

The finite all-ideal clause needs no separate positive-uniformizer-level reduction theorem,
quotient flatness, preservation of finite Tor amplitude by reduction, or purity-specific
coefficient-field presentation. Its third tensor input is arbitrary, so zero, unit and
nonperfect quotient ideals remain included.

No existing import is removed and no module or node is withdrawn. The eight unfinished
clauses and the existing structural proofs retain their dependencies and the unit's route.

## Where the brief, the DAG or earlier work was wrong

The existing `projectionFiniteReduction` wrapper treats transitions between positive
uniformizer levels on finite-Tor inputs. It does not itself give the assigned all-ideal
ambient square. The existing general proper/open tensor-action proof provides the needed
calculation, including quotients whose reduction leaves the finite-Tor domain. Its public
purity wrapper has extra coefficient-presentation restrictions; the already-proved private
coefficient-category theorem has exactly the required generality.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
