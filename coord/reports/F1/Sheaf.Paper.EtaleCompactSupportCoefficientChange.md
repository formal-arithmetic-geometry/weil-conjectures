## What changed

Filled all three existing holes of `Sheaf.Paper.EtaleCompactSupportCoefficientChange`.
The finite-Tor argument applies the amplitude interval to the constant coefficient sheaf,
then detects boundedness through exact restriction of scalars. Its adjunction unit supplies
an ordinary-etale tensor model. The scalar/site comparison and uniqueness of universal
arrows give the pro-etale origin theorem.

For compact support, first transport the universal tensor arrow through open extension
using the open adjunction and its actual mate equation. Apply the new proper-factor lemma,
then expand the specified compactification comparison. Uniqueness of universal arrows
makes the canonical B-linear comparison invertible. All existing signatures, definitions,
and public imports are unchanged. Elaboration options are scoped to individual proofs;
the static interface comparison against the original module is empty. No source-library module is edited.

Added `Sheaf.Paper.EtaleProperCoefficientTensorUnit`, proving that proper direct image
preserves the ambient universal tensor property for finite coefficient rings. Its proof
uses the existing proper projection formula, scalar/tensor mate normalization, double-mate
conjugation, and the proved `restriction_plus_mate` helper in
`Sheaf.Paper.FiniteCoefficientDirectImage`. No Noetherian or flatness assumption is added.
The new module is a separate proper-factor result, proved in this delivery.

Updated the existing node's proof with the ordinary-etale argument while retaining its
six pro-etale steps and dependencies, which still describe the imported pro-etale theorem.
The unit's route is preserved. The new node records the proper-factor proof.

## Proved and sorry left

Closed the three pre-existing holes:

- `AlgebraicGeometry.Etale.compactSupportCoefficientComparisonPlus_isIso`.
- `AlgebraicGeometry.Etale.nonempty_coefficientTensorModel_of_finiteTor`.
- `AlgebraicGeometry.ProEtale.CoefficientTensorModel.origin_of_etale_finiteTor`.

Also proved the new theorem
`AlgebraicGeometry.Etale.properCoefficientTensorUnit_universal`, node
`lem-fix-etale-proper-coefficient-tensor-unit`, and all its private helpers.
No holes remain in either delivered Lean module. Holes closed: 3; holes added: 0;
unfinished statements split off: 0. Existing imported theorems are used with their
published statements; this report does not claim to discharge their existing holes.

Validation: both delivered modules compile together through the project compile service.
The proof covers nonflat coefficient quotients, identity reductions, and identity proper
maps without changing the statements. The finite-Tor hypotheses are used only for the
bounded tensor/origin interfaces; the compact-support comparison is proved for its given
universal presentations.

## No longer needed

Removed these 25 direct proof imports from the assigned module:

- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.FixSiteOpenExchange`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`.
- `Sheaf.Paper.CondensedAmbientExchange`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.SecSmoothPurity.DirectImageScalarExchange`.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`.
- `Sheaf.SecSmoothPurity.OpenScalarExchange`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`.
- `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`.

The ordinary-etale proof does not require the original planned constructible-model,
base-change-exchange, successive-reduction, or projection-coherence routes. In particular,
it uses the finite-Tor interval directly instead of constructing a flat representative.
The proper projection-formula import is needed by the new proper-factor module, where it
is retained. Other removed direct imports can remain reachable through existing imported
modules; no whole module is withdrawn or claimed globally pruned. The shared node's
original six-step pro-etale route and its tool approvals stay, because the imported
pro-etale theorem still needs them. No DAG node is deleted. The direct import of
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` is retained because preflight
identifies it as a unit-route module; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing node's six steps described the pro-etale assembly, but the assigned module
contains ordinary-etale universal presentations and two domain/origin interfaces. The
supplement now records those actual proofs. No existing statement is disputed.

The finite-Tor docstrings had suggested flat-model constructions. They are unnecessary:
exact scalar restriction detects the homology vanishing supplied by the amplitude
interval. The revised docstrings describe the proofs actually written.

The proper-factor statement must work for arbitrary finite rings in Type(u+1), without
Noetherian scheme hypotheses. The proof therefore uses the ambient finite-coefficient
proper projection formula, rather than a more restrictive finite-dimensional direct-image
result. Its canonical D+ normalization is reused from a fully proved library helper.

## New nodes

`lem-fix-etale-proper-coefficient-tensor-unit`, in
`dag/nodes/sec-smooth-purity/lem-fix-etale-proper-coefficient-tensor-unit.json`, realized by
`AlgebraicGeometry.Etale.properCoefficientTensorUnit_universal` in the module
`Sheaf.Paper.EtaleProperCoefficientTensorUnit`. This is the proper factor of the
compactification argument, strictly smaller than compact-support coefficient change.
It is fully proved. The node has its source, five proof steps, dependency records, and
three kinds of Mathlib search. There are no definition/statement repairs or change records.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
