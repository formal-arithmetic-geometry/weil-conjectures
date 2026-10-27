## What changed

Proved four corollaries in Sheaf.Paper.ResidueCompatiblePullbackFrobenius without
changing any declaration signature or comparison construction. The immersion proof uses
the existing stronger residue-isomorphism theorem for maps surjective on stalks, the finite
point criterion, and the vector-space cardinality formula. Rational point naturality
identifies the specified compositor with the normalized natural isomorphism
fieldRationalPullComp already provided by FieldWeilShriekShiftData. Common-stage point
naturality uses the normalized zlPullComp comparison, identified componentwise with the
published localQbarPullbackComposition. Common-stage heart preservation applies zlPull_mem.
Both new helpers are private and proved; their component identities follow from the
normalization equations of the existing rational and common-stage natural isomorphisms.

Made Scheme.residueField, the two recorded pullback functors, and their explicit
alpha and fibre comparison components locally irreducible after their required elaboration to avoid
expensive quotient and choice unfolding during instance search. Disabled unused
structure size/injectivity generation. No existing source consumer refers to those
automatically generated helpers (checked across Sheaf and WeilConjectures). These
elaboration settings do not change the recorded definitions or theorem signatures. Updated the existing DAG proof to match the proved
corollaries and retain the remaining eleven-step plan.

## Proved and sorry left

Validation: the final item compiled on the project server in 51.8 seconds, exit code 0,
with no errors or warnings.

Closed four of the ten existing holes:

- WeilConjectures.ResidueCompatible.immersion_residue
- WeilConjectures.ResidueCompatible.rational_point_naturality
- WeilConjectures.ResidueCompatible.common_point_naturality
- WeilConjectures.ResidueCompatible.common_heart

Six existing holes remain unchanged, all attached to
lem-zl-residue-compatible-pullback-frobenius with their original source and proof docstrings:

- WeilConjectures.ResidueCompatible.frobenius_exact
- WeilConjectures.ResidueCompatible.residueCompatiblePullbackFrobenius
- WeilConjectures.ResidueCompatible.rational_heart
- WeilConjectures.ResidueCompatible.finite_diagram_descent
- WeilConjectures.ResidueCompatible.composition_scalar
- WeilConjectures.ResidueCompatible.transport_scalar

No holes added and no split-off statements. This is a partial delivery of a module with
several existing holes, not a claim to have proved the full residue-compatible comparison.

## No longer needed

The immersion proof does not need lem-weil-pbc-closed-immersion-residue-field-iso or an
open/closed factorization. It uses lem-weil-pbc-surjective-stalks-residue-field-iso directly.
The former proof dependency and its obsolete tool_uses entry are removed from this node.
No module is withdrawn; the unit route is unchanged.

Removed these private imports because the completed proofs do not use them directly:

- Sheaf.AlgebraicGeometry.FrobeniusDetailed
- Sheaf.Paper.SfRationalizationKaroubi
- Sheaf.AlgebraicGeometry.ClosedPointField
- Sheaf.Paper.FiniteCoefficientPoint
- Sheaf.Paper.IsomorphismDerivedPullback
- Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
- Sheaf.SixFunctors.FrobeniusPointTransportNatural
- Sheaf.Paper.ConstructiblePullbackTExact
- Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
- Sheaf.Paper.PullbackIdentitiesScalarExtension
- Sheaf.Paper.PointSectionsScalarExtension
- Sheaf.Paper.IntegralOperationsScalarComparisons

The remaining unproved clauses retain their planned dependencies in the DAG. Public
imports are unchanged. No claim is made that these transitive modules are globally unused.

## Where the brief, the DAG or earlier work was wrong

The planned immersion factorization is unnecessary: the source library already proves
that any map surjective on stalks induces the actual residue-field isomorphism. Closedness
of the image follows from the finite-residue-field criterion, without a false general
claim about closed points of open subsets. Rational naturality already follows from the
normalized fieldRationalPullComp in the publicly imported FieldWeilShriekShiftData; no new
tensor-product naturality proof or dependency on LocalFrobeniusWeilMorphismNaturality
is necessary.

The server briefly failed before Lean startup because its temporary filesystem was full;
later changed-version compilations reached Lean normally. Profiling located costly
instance search expanding Scheme.residueField, repaired by a local irreducibility setting.
The final comparison proof uses heterogeneous equality to strip equality transports
without normalizing their large object expressions.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
