## What changed

Filled the three original proof bodies in
`Sheaf.Paper.PullbackIdentitiesScalarExtension`, preserving every existing declaration
signature, definition body and public import. Added private proved categorical helpers
for adjunction mates and inversion naturality, and private proof imports for the existing
normalized counit, natural kappa, scalar agreement and whole-system mixed coherence.

The composition clause is proved for the arbitrary supplied `D`, rather than replacing
it by a system obtained from an existence theorem. Apply simultaneous whole-system
reduction, postcompose with the iterated invertible action counits, use counit naturality
and `integralQuotientMixedCoherence.derived_mixed`, and reflect equality through the
invertible actual completion unit on the constructible target. This is equality in the
derived category of entire quotient systems, never separate finite-reduction detection.

For the inverse clause, cancel the specified kappas in the existing scalar square,
prove naturality of their inverses and the specified beta components, and paste with
`completedInverseImage_scalarCounit`. The two section-normalized counit definitions
agree by their uniqueness theorems. No comparison map is chosen arbitrarily.

## Proved and sorry left

Closed the original holes in:

- `WeilConjectures.pullbackIdentityModuleCounit_existsUnique`.
- `WeilConjectures.pullbackIdentityKappa_isIso`.
- `WeilConjectures.pullbackIdentities_scalarExtension`.

All belong to `lem-pod-pullback-identities-scalar-extension`. Three holes closed;
zero holes added or split off; zero `sorry` remains in the delivered module.
The proofs use the existing named dependency statements, some of which remain open.
The complete module compiled with no warnings and no remaining holes. Delivery
validation also checks the compiled consumer and the dependency ledger.

## No longer needed

No existing public import was removed, and no module is withdrawn. Removed the unused
private proof import `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
`lem-pod-inverse-comparison-counit-transport` and its module
`Sheaf.CategoryTheory.InverseComparisonCounitTransport` are unnecessary for this proof:
the componentwise categorical pasting is proved directly by private helpers, avoiding
construction of four full-subcategory functor equivalences.

The proof does not directly invoke
`lem-weil-isomorphism-derived-pullback`,
`lem-weil-proetale-isomorphism-inverse-image`,
`lem-weil-isomorphism-derived-pullback-comparison-normalization`, or
`lem-weil-finite-free-completed-scalar-comparison` as extra black boxes.
Their consequences needed here are already supplied by the natural-kappa,
scalar-comparison and normalized-counit dependencies. Existing public imports and
transitive dependency uses remain; these modules are not claimed globally pruned.
Removed obsolete direct tool approvals for the first three from this node only.

## Where the brief, the DAG or earlier work was wrong

The first planned application of integral pullback realization has a quantifier gap:
the realization theorem asserts existence of a coherent system, while this item's
statement supplies an arbitrary system `D`. Its coherence conclusion cannot simply
be applied to that `D`. The direct counit-mate calculation establishes the desired
mixed square for the supplied system without altering either statement.

The node's proposed categorical transport theorem requires natural isomorphisms of
functors between the full constructible categories. The componentwise proof needs
only the natural specified kappa and beta on the indicated constructible inputs.
All intermediate inputs are explicitly typed using
`isomorphismComparisonInputs_constructible`; no geometric assumption is dropped.
The unit record `sk-lem-finite` has no realization of this node, and its route and
all target statements are unchanged. No source-library file is edited.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
